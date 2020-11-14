//! Easily retry futures.
//!
//! ## Example usage
//!
//! ```
//! use tryhard::RetryFuture;
//!
//! // some async function that can fail
//! async fn read_file(path: &str) -> Result<String, std::io::Error> {
//!     // ...
//!     # Ok("tryhard".to_string())
//! }
//!
//! # futures::executor::block_on(async_try_main()).unwrap();
//! #
//! # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
//! let contents = RetryFuture::new(
//!     // the max number of retries
//!     10,
//!     // closure that produces the future to retry
//!     || read_file("Cargo.toml"),
//! ).await?;
//!
//! assert!(contents.contains("tryhard"));
//! # Ok(())
//! # }
//! ```
//!
//! Through `RetryFutureExt` you can call `.retry` directly on a closure:
//!
//! ```
//! use tryhard::RetryFutureExt;
//!
//! # async fn read_file(path: &str) -> Result<String, std::io::Error> {
//! #     Ok("tryhard".to_string())
//! # }
//! # futures::executor::block_on(async_try_main()).unwrap();
//! #
//! # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
//! let contents = (|| read_file("Cargo.toml")).retry(10).await?;
//!
//! assert!(contents.contains("tryhard"));
//! # Ok(())
//! # }
//! ```
//!
//! You can also customize which backoff strategy to use and what the max retry delay should be:
//!
//! ```
//! use std::time::Duration;
//! use tryhard::RetryFutureExt;
//!
//! # async fn read_file(path: &str) -> Result<String, std::io::Error> {
//! #     Ok("tryhard".to_string())
//! # }
//! # futures::executor::block_on(async_try_main()).unwrap();
//! #
//! # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
//! let contents = (|| read_file("Cargo.toml"))
//!     .retry(10)
//!     .exponential_backoff(Duration::from_millis(10))
//!     .max_delay(Duration::from_secs(1))
//!     .await?;
//!
//! assert!(contents.contains("tryhard"));
//! # Ok(())
//! # }
//! ```
//!
//! ## How many times will my future run?
//!
//! The future is always run at least once, so if you do `.retry(0)` your future will run once.
//! If you do `.retry(10)` and your future always fails it'll run 11 times.
//!
//! ## Why do you require a closure?
//!
//! Due to how futures work in Rust you're not able to retry a bare `F where F: Future`. A future
//! can possibly fail at any point in its execution and might be in an inconsistent state after the
//! failing. Therefore retrying requires making a fresh future for each attempt.
//!
//! This means you cannot move values into the closure that produces the futures. You'll have to
//! clone instead:
//!
//! ```
//! use tryhard::RetryFutureExt;
//!
//! async fn future_with_owned_data(data: Vec<u8>) -> Result<(), std::io::Error> {
//!     // ...
//!     # Ok(())
//! }
//!
//! # futures::executor::block_on(async_try_main()).unwrap();
//! #
//! # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
//! let data: Vec<u8> = vec![1, 2, 3];
//!
//! (|| {
//!     // We need to clone `data` here. Otherwise we would have to move `data` into the closure.
//!     // `move` closures can only be called once (they only implement `FnOnce`)
//!     // and therefore cannot be used to create more than one future.
//!     let data = data.clone();
//!
//!     async {
//!         future_with_owned_data(data).await
//!     }
//! }).retry(10).await?;
//! # Ok(())
//! # }
//! ```
//!
//! ## Tokio only for now
//!
//! This library currently expects to be used from within a [tokio](https://tokio.rs) runtime. That
//! is because it makes use of async timers. Feel free to open an issue if you need support for
//! other runtimes.

#![warn(missing_docs)]

use futures::ready;
use pin_project::pin_project;
use std::{
    fmt::Display,
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};
use std::{marker::PhantomData, time::Duration};
use tokio::time;

/// A retryable future.
#[pin_project]
pub struct RetryFuture<F, Fut, T, E> {
    make_future: F,
    attempts_remaining: u32,
    backoff_strategy: BackoffStrategy<E>,
    max_delay: Option<Duration>,
    #[pin]
    state: RetryState<Fut>,
    attempt: u32,
    _marker: PhantomData<(Fut, T)>,
}

impl<F, Fut, T, E> RetryFuture<F, Fut, T, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    /// Create a new `RetryFuture` given the max number of times to retry and a closure that
    /// produces the future to run.
    pub fn new(max_retries: u32, make_future: F) -> Self {
        Self {
            make_future,
            attempts_remaining: max_retries,
            backoff_strategy: BackoffStrategy::None,
            max_delay: None,
            state: RetryState::NotStarted,
            attempt: 0,
            _marker: PhantomData,
        }
    }

    /// Set the max duration to sleep between each attempt.
    pub fn max_delay(mut self, delay: Duration) -> Self {
        self.max_delay = Some(delay);
        self
    }

    /// Remove the backoff strategy.
    ///
    /// This will make the future be retried immediately without any delay in between attempts.
    pub fn no_backoff(mut self) -> Self {
        self.backoff_strategy = BackoffStrategy::None;
        self
    }

    /// Use exponential backoff for retrying the future.
    ///
    /// The first delay will be `initial_delay` and afterwards the delay will double every time.
    pub fn exponential_backoff(mut self, initial_delay: Duration) -> Self {
        self.backoff_strategy = BackoffStrategy::Exponential {
            delay: initial_delay,
        };
        self
    }

    /// Use a fixed backoff for retrying the future.
    ///
    /// The delay between attempts will always be `delay`.
    pub fn fixed_backoff(mut self, delay: Duration) -> Self {
        self.backoff_strategy = BackoffStrategy::Fixed { delay };
        self
    }

    /// Use a linear backoff for retrying the future.
    ///
    /// The delay will be `delay * attempt` so it'll scale linear with the attempt.
    pub fn linear_backoff(mut self, delay: Duration) -> Self {
        self.backoff_strategy = BackoffStrategy::Linear { delay };
        self
    }

    /// Use a custom backoff specified by some function.
    ///
    /// ```
    /// use std::time::Duration;
    /// use tryhard::RetryFutureExt;
    ///
    /// # async fn read_file(path: &str) -> Result<String, std::io::Error> {
    /// #     todo!()
    /// # }
    /// #
    /// # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
    /// (|| read_file("Cargo.toml"))
    ///     .retry(3)
    ///     .custom_backoff(|attempt, error| {
    ///         if error.to_string().contains("foo") {
    ///             Duration::from_millis(100)
    ///         } else {
    ///             Duration::from_secs(1)
    ///         }
    ///     })
    ///     .await?;
    /// # Ok(())
    /// # }
    pub fn custom_backoff<Fun>(mut self, f: Fun) -> Self
    where
        Fun: 'static + FnMut(u32, &E) -> Duration + Send,
    {
        self.backoff_strategy = BackoffStrategy::Custom(Box::new(f));
        self
    }
}

#[pin_project(project = RetryStateProj)]
enum RetryState<F> {
    NotStarted,
    WaitingForFuture(#[pin] F),
    TimerActive(#[pin] time::Delay),
}

impl<F, Fut, T, E> Future for RetryFuture<F, Fut, T, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: Display,
{
    type Output = Result<T, E>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        loop {
            let this = self.as_mut().project();

            let new_state = match this.state.project() {
                RetryStateProj::NotStarted => RetryState::WaitingForFuture((this.make_future)()),

                RetryStateProj::TimerActive(delay) => {
                    ready!(delay.poll(cx));
                    RetryState::WaitingForFuture((this.make_future)())
                }

                RetryStateProj::WaitingForFuture(fut) => {
                    match ready!(fut.poll(cx)) {
                        Ok(value) => {
                            return Poll::Ready(Ok(value));
                        }
                        Err(error) => {
                            if *this.attempts_remaining == 0 {
                                return Poll::Ready(Err(error));
                            } else {
                                *this.attempt += 1;
                                *this.attempts_remaining -= 1;

                                // rust-analyzer gets confused if you don't declare the type here
                                let mut delay_duration: Duration =
                                    this.backoff_strategy.delay(*this.attempt, &error);
                                if let Some(max_delay) = this.max_delay {
                                    delay_duration = delay_duration.min(*max_delay);
                                }

                                log::error!(
                                    "Future failed. Retrying again in {:?}. Error: {}. Attempts remaining = {}",
                                    delay_duration,
                                    error,
                                    self.attempts_remaining,
                                );

                                let delay = time::delay_for(delay_duration);
                                RetryState::TimerActive(delay)
                            }
                        }
                    }
                }
            };

            self.as_mut().project().state.set(new_state);
        }
    }
}

enum BackoffStrategy<E> {
    None,
    Exponential { delay: Duration },
    Fixed { delay: Duration },
    Linear { delay: Duration },
    Custom(Box<dyn FnMut(u32, &E) -> Duration + Send>),
}

impl<E> BackoffStrategy<E> {
    fn delay(&mut self, attempt: u32, error: &E) -> Duration {
        match self {
            BackoffStrategy::None => Duration::new(0, 0),
            BackoffStrategy::Exponential { delay } => {
                let prev_delay = *delay;
                *delay *= 2;
                prev_delay
            }
            BackoffStrategy::Fixed { delay } => *delay,
            BackoffStrategy::Linear { delay } => *delay * attempt,
            BackoffStrategy::Custom(f) => f(attempt, error),
        }
    }
}

/// Extension trait that adds a `retry` method to all `FnMut() -> impl Future<Output = Result<T, E>>`.
pub trait RetryFutureExt<Fut, T, E>: Sized {
    /// Construct a retryable future.
    fn retry(self, max_retries: u32) -> RetryFuture<Self, Fut, T, E>;
}

impl<F, Fut, T, E> RetryFutureExt<Fut, T, E> for F
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    fn retry(self, max_retries: u32) -> RetryFuture<Self, Fut, T, E> {
        RetryFuture::new(max_retries, self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::{convert::Infallible, time::Instant};

    #[tokio::test]
    async fn succeed() {
        RetryFuture::new(10, || async { Ok::<_, Infallible>(true) })
            .await
            .unwrap();
    }

    #[tokio::test]
    async fn retrying_correct_amount_of_times() {
        let counter = AtomicUsize::new(0);

        let err = RetryFuture::new(10, || async {
            counter.fetch_add(1, Ordering::SeqCst);
            Err::<Infallible, _>("error")
        })
        .await
        .unwrap_err();

        assert_eq!(err, "error");
        assert_eq!(counter.load(Ordering::Relaxed), 11);
    }

    #[tokio::test]
    async fn retry_0_times() {
        let counter = AtomicUsize::new(0);

        RetryFuture::new(0, || async {
            counter.fetch_add(1, Ordering::SeqCst);
            Err::<Infallible, _>("error")
        })
        .await
        .unwrap_err();

        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[tokio::test]
    async fn the_backoff_strategy_gets_used() {
        async fn make_future() -> Result<Infallible, &'static str> {
            Err("foo")
        }

        let start = Instant::now();
        RetryFuture::new(10, make_future)
            .no_backoff()
            .await
            .unwrap_err();
        let time_with_none = start.elapsed();

        let start = Instant::now();
        RetryFuture::new(10, make_future)
            .fixed_backoff(Duration::from_millis(10))
            .await
            .unwrap_err();
        let time_with_fixed = start.elapsed();

        // assertions about what the exact times are are very finicky so lets just assert that the
        // one without backoff is slower.
        assert!(time_with_fixed > time_with_none);
    }

    // `RetryFuture` must be `Send` to be used with `async_trait`
    // Generally we also want our futures to be `Send`
    #[test]
    fn is_send() {
        fn assert_send<T: Send>(_: T) {}
        async fn some_future() -> Result<(), Infallible> {
            Ok(())
        }
        assert_send(some_future.retry(10));
    }
}
