//! Easily retry futures.
//!
//! ## Example usage
//!
//! ```
//! // some async function that can fail
//! async fn read_file(path: &str) -> Result<String, std::io::Error> {
//!     // ...
//!     # Ok("tryhard".to_string())
//! }
//!
//! # futures::executor::block_on(async_try_main()).unwrap();
//! #
//! # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
//! let contents = tryhard::retry_fn(|| read_file("Cargo.toml"))
//!     // retry at most 10 times
//!     .retries(10)
//!     .await?;
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
//!
//! # async fn read_file(path: &str) -> Result<String, std::io::Error> {
//! #     Ok("tryhard".to_string())
//! # }
//! # futures::executor::block_on(async_try_main()).unwrap();
//! #
//! # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
//! let contents = tryhard::retry_fn(|| read_file("Cargo.toml"))
//!     .retries(10)
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
//! The future is always run at least once, so if you do `.retries(0)` your future will run once.
//! If you do `.retries(10)` and your future always fails it'll run 11 times.
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
//! tryhard::retry_fn(|| {
//!     // We need to clone `data` here. Otherwise we would have to move `data` into the closure.
//!     // `move` closures can only be called once (they only implement `FnOnce`)
//!     // and therefore cannot be used to create more than one future.
//!     let data = data.clone();
//!
//!     async {
//!         future_with_owned_data(data).await
//!     }
//! }).retries(10).await?;
//! # Ok(())
//! # }
//! ```
//!
//! ## Be careful what you retry
//!
//! This library is meant to make it straight forward to retry simple futures, such as sending a
//! single request to some service that occationally fails. If you have some complex operation that
//! consists of multiple futures each of which can fail, this library might be not appropriate. You
//! risk repeating the same operation more than once because some later operation keeps failing.
//!
//! ## Tokio only for now
//!
//! This library currently expects to be used from within a [tokio](https://tokio.rs) runtime. That
//! is because it makes use of async timers. Feel free to open an issue if you need support for
//! other runtimes.
//!
//! [`RetryFuture`]: struct.RetryFuture.html

#![warn(missing_docs)]
#![forbid(unsafe_code)]

use backoff_strategies::{
    BackoffStrategy, CustomBackoffStrategy, ExponentialBackoff, FixedBackoff, LinearBackoff,
    NoBackoff,
};
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

pub mod backoff_strategies;

/// Create a `RetryFn` which produces retryable futures.
pub fn retry_fn<F>(f: F) -> RetryFn<F> {
    RetryFn { f }
}

/// A type that produces retryable futures.
#[derive(Debug)]
pub struct RetryFn<F> {
    f: F,
}

impl<F> RetryFn<F> {
    /// Specify the number of times to retry the future.
    pub fn retries<Fut, T, E>(self, max_retries: u32) -> RetryFuture<F, Fut, NoBackoff, T, E>
    where
        F: FnMut() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        RetryFuture {
            make_future: self.f,
            attempts_remaining: max_retries,
            backoff_strategy: NoBackoff,
            max_delay: None,
            state: RetryState::NotStarted,
            attempt: 0,
            _marker: PhantomData,
        }
    }
}

/// A retryable future.
///
/// Can be created by calling [`retry_fn`](fn.retry_fn.html).
#[pin_project]
pub struct RetryFuture<F, Fut, B, T, E> {
    make_future: F,
    attempts_remaining: u32,
    backoff_strategy: B,
    max_delay: Option<Duration>,
    #[pin]
    state: RetryState<Fut>,
    attempt: u32,
    _marker: PhantomData<(Fut, T, E)>,
}

impl<F, Fut, B, T, E> RetryFuture<F, Fut, B, T, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    /// Set the max duration to sleep between each attempt.
    #[inline]
    pub fn max_delay(mut self, delay: Duration) -> Self {
        self.max_delay = Some(delay);
        self
    }

    /// Remove the backoff strategy.
    ///
    /// This will make the future be retried immediately without any delay in between attempts.
    #[inline]
    pub fn no_backoff(self) -> RetryFuture<F, Fut, NoBackoff, T, E> {
        self.with_backoff(NoBackoff)
    }

    /// Use exponential backoff for retrying the future.
    ///
    /// The first delay will be `initial_delay` and afterwards the delay will double every time.
    #[inline]
    pub fn exponential_backoff(
        self,
        initial_delay: Duration,
    ) -> RetryFuture<F, Fut, ExponentialBackoff, T, E> {
        self.with_backoff(ExponentialBackoff {
            delay: initial_delay,
        })
    }

    /// Use a fixed backoff for retrying the future.
    ///
    /// The delay between attempts will always be `delay`.
    #[inline]
    pub fn fixed_backoff(self, delay: Duration) -> RetryFuture<F, Fut, FixedBackoff, T, E> {
        self.with_backoff(FixedBackoff { delay })
    }

    /// Use a linear backoff for retrying the future.
    ///
    /// The delay will be `delay * attempt` so it'll scale linear with the attempt.
    #[inline]
    pub fn linear_backoff(self, delay: Duration) -> RetryFuture<F, Fut, LinearBackoff, T, E> {
        self.with_backoff(LinearBackoff { delay })
    }

    /// Use a custom backoff specified by some function.
    ///
    /// ```
    /// use std::time::Duration;
    ///
    /// # async fn read_file(path: &str) -> Result<String, std::io::Error> {
    /// #     todo!()
    /// # }
    /// #
    /// # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
    /// tryhard::retry_fn(|| read_file("Cargo.toml"))
    ///     .retries(10)
    ///     .custom_backoff(|attempt, _error| {
    ///         if attempt < 5 {
    ///             Duration::from_millis(100)
    ///         } else {
    ///             Duration::from_millis(500)
    ///         }
    ///     })
    ///     .await?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// You can also stop retrying early:
    ///
    /// ```
    /// use std::time::Duration;
    /// use tryhard::RetryPolicy;
    ///
    /// # async fn read_file(path: &str) -> Result<String, std::io::Error> {
    /// #     todo!()
    /// # }
    /// #
    /// # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
    /// tryhard::retry_fn(|| read_file("Cargo.toml"))
    ///     .retries(10)
    ///     .custom_backoff(|attempt, error| {
    ///         if error.to_string().contains("foobar") {
    ///             // returning this will cancel the loop and
    ///             // return the most recent error
    ///             RetryPolicy::Break
    ///         } else {
    ///             RetryPolicy::Delay(Duration::from_millis(50))
    ///         }
    ///     })
    ///     .await?;
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn custom_backoff<Fun, R>(
        self,
        f: Fun,
    ) -> RetryFuture<F, Fut, CustomBackoffStrategy<Fun>, T, E>
    where
        Fun: FnMut(u32, &E) -> R,
        RetryPolicy: From<R>,
    {
        self.with_backoff(CustomBackoffStrategy { f })
    }

    #[inline]
    fn with_backoff<B2>(self, backoff_strategy: B2) -> RetryFuture<F, Fut, B2, T, E> {
        RetryFuture {
            make_future: self.make_future,
            attempts_remaining: self.attempts_remaining,
            backoff_strategy,
            max_delay: self.max_delay,
            state: self.state,
            attempt: self.attempt,
            _marker: self._marker,
        }
    }
}

#[pin_project(project = RetryStateProj)]
enum RetryState<F> {
    NotStarted,
    WaitingForFuture(#[pin] F),
    TimerActive(#[pin] time::Delay),
}

impl<F, Fut, B, T, E> Future for RetryFuture<F, Fut, B, T, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: Display,
    B: BackoffStrategy<E>,
    RetryPolicy: From<B::Output>,
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

                RetryStateProj::WaitingForFuture(fut) => match ready!(fut.poll(cx)) {
                    Ok(value) => {
                        return Poll::Ready(Ok(value));
                    }
                    Err(error) => {
                        if *this.attempts_remaining == 0 {
                            return Poll::Ready(Err(error));
                        } else {
                            *this.attempt += 1;
                            *this.attempts_remaining -= 1;

                            let delay = RetryPolicy::from(
                                this.backoff_strategy.delay(*this.attempt, &error),
                            );
                            let mut delay_duration = match delay {
                                RetryPolicy::Delay(duration) => duration,
                                RetryPolicy::Break => return Poll::Ready(Err(error)),
                            };

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
                },
            };

            self.as_mut().project().state.set(new_state);
        }
    }
}

/// What to do when a future returns an error. Used with [`RetryFuture::custom`].
///
/// [`RetryFuture::custom`]: struct.RetryFuture.html#method.custom_backoff
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum RetryPolicy {
    /// Try again in the specified `Duration`.
    Delay(Duration),

    /// Don't retry.
    Break,
}

impl From<Duration> for RetryPolicy {
    fn from(duration: Duration) -> Self {
        RetryPolicy::Delay(duration)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::{convert::Infallible, time::Instant};

    #[tokio::test]
    async fn succeed() {
        retry_fn(|| async { Ok::<_, Infallible>(true) })
            .retries(10)
            .await
            .unwrap();
    }

    #[tokio::test]
    async fn retrying_correct_amount_of_times() {
        let counter = AtomicUsize::new(0);

        let err = retry_fn(|| async {
            counter.fetch_add(1, Ordering::SeqCst);
            Err::<Infallible, _>("error")
        })
        .retries(10)
        .await
        .unwrap_err();

        assert_eq!(err, "error");
        assert_eq!(counter.load(Ordering::Relaxed), 11);
    }

    #[tokio::test]
    async fn retry_0_times() {
        let counter = AtomicUsize::new(0);

        retry_fn(|| async {
            counter.fetch_add(1, Ordering::SeqCst);
            Err::<Infallible, _>("error")
        })
        .retries(0)
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
        retry_fn(make_future)
            .retries(10)
            .no_backoff()
            .await
            .unwrap_err();
        let time_with_none = start.elapsed();

        let start = Instant::now();
        retry_fn(make_future)
            .retries(10)
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
        assert_send(retry_fn(some_future).retries(10));
    }

    #[tokio::test]
    async fn stop_retrying() {
        let mut n = 0;
        let make_future = || {
            n += 1;
            if n == 8 {
                panic!("retried too many times");
            }
            async { Err::<Infallible, _>("foo") }
        };

        let error = retry_fn(make_future)
            .retries(10)
            .custom_backoff(|n, _| {
                if n >= 3 {
                    RetryPolicy::Break
                } else {
                    RetryPolicy::Delay(Duration::from_nanos(10))
                }
            })
            .await
            .unwrap_err();

        assert_eq!(error, "foo");
    }

    #[tokio::test]
    async fn custom_returning_duration() {
        retry_fn(|| async { Ok::<_, Infallible>(true) })
            .retries(10)
            .custom_backoff(|_, _| Duration::from_nanos(10))
            .await
            .unwrap();
    }
}
