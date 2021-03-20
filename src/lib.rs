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
//! ## Retrying several futures in the same way
//!
//! Using [`RetryFutureConfig`] you're able to retry several futures in the same way:
//!
//! ```
//! # use std::time::Duration;
//! # async fn read_file(path: &str) -> Result<String, std::io::Error> {
//! #     Ok("tryhard".to_string())
//! # }
//! #
//! # futures::executor::block_on(async_try_main()).unwrap();
//! #
//! # async fn async_try_main() -> Result<(), Box<dyn std::error::Error>> {
//! use tryhard::RetryFutureConfig;
//!
//! let config = RetryFutureConfig::new(10)
//!     .exponential_backoff(Duration::from_millis(10))
//!     .max_delay(Duration::from_secs(3));
//!
//! tryhard::retry_fn(|| read_file("Cargo.toml"))
//!     .with_config(config)
//!     .await?;
//!
//! // retry another future in the same way
//! tryhard::retry_fn(|| read_file("src/lib.rs"))
//!     .with_config(config)
//!     .await?;
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
//! By default it uses Tokio 1.0. You can switch to Tokio 0.2 by disabling default features and
//! enabling the `tokio-02` feature:
//!
//! ```toml
//! tryhard = { version = "your-version", default-features = false, features = ["tokio-02"] }
//! ```
//!
//! Note that enabling both Tokio 1.0 and 0.2 will cause a compilation error.
//!
//! Tokio 0.3 is not supported.
//!
//! [`RetryFuture`]: struct.RetryFuture.html

// BEGIN - Embark standard lints v0.3
// do not change or add/remove here, but one can add exceptions after this section
// for more info see: <https://github.com/EmbarkStudios/rust-ecosystem/issues/59>
#![deny(unsafe_code)]
#![warn(
    clippy::all,
    clippy::await_holding_lock,
    clippy::dbg_macro,
    clippy::debug_assert_with_mut_call,
    clippy::doc_markdown,
    clippy::empty_enum,
    clippy::enum_glob_use,
    clippy::exit,
    clippy::explicit_into_iter_loop,
    clippy::filter_map_next,
    clippy::fn_params_excessive_bools,
    clippy::if_let_mutex,
    clippy::imprecise_flops,
    clippy::inefficient_to_string,
    clippy::large_types_passed_by_value,
    clippy::let_unit_value,
    clippy::linkedlist,
    clippy::lossy_float_literal,
    clippy::macro_use_imports,
    clippy::map_err_ignore,
    clippy::map_flatten,
    clippy::map_unwrap_or,
    clippy::match_on_vec_items,
    clippy::match_same_arms,
    clippy::match_wildcard_for_single_variants,
    clippy::mem_forget,
    clippy::mismatched_target_os,
    clippy::needless_borrow,
    clippy::needless_continue,
    clippy::option_option,
    clippy::pub_enum_variant_names,
    clippy::ref_option_ref,
    clippy::rest_pat_in_fully_bound_structs,
    clippy::string_add_assign,
    clippy::string_add,
    clippy::string_to_string,
    clippy::suboptimal_flops,
    clippy::todo,
    clippy::unimplemented,
    clippy::unnested_or_patterns,
    clippy::unused_self,
    clippy::verbose_file_reads,
    future_incompatible,
    nonstandard_style,
    rust_2018_idioms
)]
// END - Embark standard lints v0.3

use backoff_strategies::{
    BackoffStrategy, CustomBackoffStrategy, ExponentialBackoff, FixedBackoff, LinearBackoff,
    NoBackoff,
};
use futures::future::Ready;
use futures::ready;
use pin_project::pin_project;
use std::{convert::Infallible, time::Duration};
use std::{
    fmt,
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

#[cfg(all(feature = "tokio-02", feature = "tokio-1"))]
compile_error!("Cannot enable both tokio-02 and tokio-1 features");

#[cfg(feature = "tokio-1")]
use tokio_1 as tokio;

#[cfg(feature = "tokio-02")]
use tokio_02 as tokio;

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

impl<F, Fut, T, E> RetryFn<F>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    /// Specify the number of times to retry the future.
    pub fn retries(self, max_retries: u32) -> RetryFuture<F, Fut, NoBackoff, NoOnRetry> {
        self.with_config(RetryFutureConfig::new(max_retries))
    }

    /// Create a retryable future from the given configuration.
    pub fn with_config<BackoffT, OnRetryT>(
        self,
        config: RetryFutureConfig<BackoffT, OnRetryT>,
    ) -> RetryFuture<F, Fut, BackoffT, OnRetryT> {
        RetryFuture {
            make_future: self.f,
            attempts_remaining: config.max_retries,
            state: RetryState::NotStarted,
            attempt: 0,
            config,
        }
    }
}

/// A retryable future.
///
/// Can be created by calling [`retry_fn`](fn.retry_fn.html).
#[pin_project]
pub struct RetryFuture<MakeFutureT, FutureT, BackoffT, OnRetryT> {
    make_future: MakeFutureT,
    attempts_remaining: u32,
    #[pin]
    state: RetryState<FutureT>,
    attempt: u32,
    config: RetryFutureConfig<BackoffT, OnRetryT>,
}

impl<MakeFutureT, FutureT, BackoffT, T, E, OnRetryT>
    RetryFuture<MakeFutureT, FutureT, BackoffT, OnRetryT>
where
    MakeFutureT: FnMut() -> FutureT,
    FutureT: Future<Output = Result<T, E>>,
{
    /// Set the max duration to sleep between each attempt.
    #[inline]
    pub fn max_delay(mut self, delay: Duration) -> Self {
        self.config = self.config.max_delay(delay);
        self
    }

    /// Remove the backoff strategy.
    ///
    /// This will make the future be retried immediately without any delay in between attempts.
    #[inline]
    pub fn no_backoff(self) -> RetryFuture<MakeFutureT, FutureT, NoBackoff, OnRetryT> {
        self.with_backoff(NoBackoff)
    }

    /// Use exponential backoff for retrying the future.
    ///
    /// The first delay will be `initial_delay` and afterwards the delay will double every time.
    #[inline]
    pub fn exponential_backoff(
        self,
        initial_delay: Duration,
    ) -> RetryFuture<MakeFutureT, FutureT, ExponentialBackoff, OnRetryT> {
        self.with_backoff(ExponentialBackoff {
            delay: initial_delay,
        })
    }

    /// Use a fixed backoff for retrying the future.
    ///
    /// The delay between attempts will always be `delay`.
    #[inline]
    pub fn fixed_backoff(
        self,
        delay: Duration,
    ) -> RetryFuture<MakeFutureT, FutureT, FixedBackoff, OnRetryT> {
        self.with_backoff(FixedBackoff { delay })
    }

    /// Use a linear backoff for retrying the future.
    ///
    /// The delay will be `delay * attempt` so it'll scale linear with the attempt.
    #[inline]
    pub fn linear_backoff(
        self,
        delay: Duration,
    ) -> RetryFuture<MakeFutureT, FutureT, LinearBackoff, OnRetryT> {
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
    pub fn custom_backoff<F, R>(
        self,
        f: F,
    ) -> RetryFuture<MakeFutureT, FutureT, CustomBackoffStrategy<F>, OnRetryT>
    where
        F: FnMut(u32, &E) -> R,
        R: Into<RetryPolicy>,
    {
        self.with_backoff(CustomBackoffStrategy { f })
    }

    /// Some async computation that will be spawned before each retry.
    ///
    /// This can for example be used for telemtry such as logging or other kinds of tracking.
    ///
    /// The future returned will be given to `tokio::spawn` so wont impact the actual retrying.
    ///
    /// ## Example
    ///
    /// For example to print and gather all the errors you can do:
    ///
    /// ```
    /// use std::sync::Arc;
    /// #[cfg(feature = "tokio-1")]
    /// use tokio_1 as tokio;
    /// #[cfg(feature = "tokio-02")]
    /// use tokio_02 as tokio;
    /// use tokio::sync::Mutex;
    ///
    /// # #[cfg_attr(feature = "tokio-1", tokio::main(flavor = "current_thread"))]
    /// # #[cfg_attr(feature = "tokio-02", tokio::main)]
    /// # async fn main() {
    /// let all_errors = Arc::new(Mutex::new(Vec::new()));
    ///
    /// tryhard::retry_fn(|| async {
    ///     // just some dummy computation that always fails
    ///     Err::<(), _>("fail")
    /// })
    ///     .retries(10)
    ///     .on_retry(|_attempt, _next_delay, error| {
    ///         // the future must be `'static` so it cannot contain references
    ///         let all_errors = Arc::clone(&all_errors);
    ///         let error = error.clone();
    ///         async move {
    ///             eprintln!("Something failed: {}", error);
    ///             all_errors.lock().await.push(error);
    ///         }
    ///     })
    ///     .await
    ///     .unwrap_err();
    ///
    /// assert_eq!(all_errors.lock().await.len(), 10);
    /// # }
    /// ```
    #[inline]
    pub fn on_retry<F, OnRetryFuture>(self, f: F) -> RetryFuture<MakeFutureT, FutureT, BackoffT, F>
    where
        F: FnMut(u32, Option<Duration>, &E) -> OnRetryFuture,
        OnRetryFuture: Future + Send + 'static,
        OnRetryFuture::Output: Send + 'static,
    {
        RetryFuture {
            make_future: self.make_future,
            attempts_remaining: self.attempts_remaining,
            state: self.state,
            attempt: self.attempt,
            config: self.config.on_retry(f),
        }
    }

    #[inline]
    fn with_backoff<BackoffT2>(
        self,
        backoff_strategy: BackoffT2,
    ) -> RetryFuture<MakeFutureT, FutureT, BackoffT2, OnRetryT> {
        RetryFuture {
            make_future: self.make_future,
            attempts_remaining: self.attempts_remaining,
            state: self.state,
            attempt: self.attempt,
            config: self.config.with_backoff(backoff_strategy),
        }
    }
}

/// Configuration describing how to retry a future.
///
/// This is useful if you have many futures you want to retry in the same way.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct RetryFutureConfig<BackoffT, OnRetryT> {
    backoff_strategy: BackoffT,
    max_delay: Option<Duration>,
    on_retry: Option<OnRetryT>,
    max_retries: u32,
}

impl RetryFutureConfig<NoBackoff, NoOnRetry> {
    /// Create a new configuration with a max number of retries and no backoff strategy.
    pub fn new(max_retries: u32) -> Self {
        Self {
            backoff_strategy: NoBackoff,
            max_delay: None,
            on_retry: None::<NoOnRetry>,
            max_retries,
        }
    }
}

impl<BackoffT, OnRetryT> RetryFutureConfig<BackoffT, OnRetryT> {
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
    pub fn no_backoff(self) -> RetryFutureConfig<NoBackoff, OnRetryT> {
        self.with_backoff(NoBackoff)
    }

    /// Use exponential backoff for retrying the future.
    ///
    /// The first delay will be `initial_delay` and afterwards the delay will double every time.
    #[inline]
    pub fn exponential_backoff(
        self,
        initial_delay: Duration,
    ) -> RetryFutureConfig<ExponentialBackoff, OnRetryT> {
        self.with_backoff(ExponentialBackoff {
            delay: initial_delay,
        })
    }

    /// Use a fixed backoff for retrying the future.
    ///
    /// The delay between attempts will always be `delay`.
    #[inline]
    pub fn fixed_backoff(self, delay: Duration) -> RetryFutureConfig<FixedBackoff, OnRetryT> {
        self.with_backoff(FixedBackoff { delay })
    }

    /// Use a linear backoff for retrying the future.
    ///
    /// The delay will be `delay * attempt` so it'll scale linear with the attempt.
    #[inline]
    pub fn linear_backoff(self, delay: Duration) -> RetryFutureConfig<LinearBackoff, OnRetryT> {
        self.with_backoff(LinearBackoff { delay })
    }

    /// Use a custom backoff specified by some function.
    ///
    /// See [`RetryFuture::custom_backoff`] for more details.
    #[inline]
    pub fn custom_backoff<F, R, E>(
        self,
        f: F,
    ) -> RetryFutureConfig<CustomBackoffStrategy<F>, OnRetryT>
    where
        F: FnMut(u32, &E) -> R,
        R: Into<RetryPolicy>,
    {
        self.with_backoff(CustomBackoffStrategy { f })
    }

    /// Some async computation that will be spawned before each retry.
    ///
    /// See [`RetryFuture::on_retry`] for more details.
    #[inline]
    pub fn on_retry<F, OnRetryFuture, E>(self, f: F) -> RetryFutureConfig<BackoffT, F>
    where
        F: FnMut(u32, Option<Duration>, &E) -> OnRetryFuture,
        OnRetryFuture: Future + Send + 'static,
        OnRetryFuture::Output: Send + 'static,
    {
        RetryFutureConfig {
            backoff_strategy: self.backoff_strategy,
            max_delay: self.max_delay,
            max_retries: self.max_retries,
            on_retry: Some(f),
        }
    }

    #[inline]
    fn with_backoff<BackoffT2>(
        self,
        backoff_strategy: BackoffT2,
    ) -> RetryFutureConfig<BackoffT2, OnRetryT> {
        RetryFutureConfig {
            backoff_strategy,
            max_delay: self.max_delay,
            max_retries: self.max_retries,
            on_retry: self.on_retry,
        }
    }
}

impl<BackoffT, OnRetryT> fmt::Debug for RetryFutureConfig<BackoffT, OnRetryT>
where
    BackoffT: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RetryFutureConfig")
            .field("backoff_strategy", &self.backoff_strategy)
            .field("max_delay", &self.max_delay)
            .field("max_retries", &self.max_retries)
            .field(
                "on_retry",
                &format_args!("<{}>", std::any::type_name::<OnRetryT>()),
            )
            .finish()
    }
}

#[allow(clippy::large_enum_variant)]
#[pin_project(project = RetryStateProj)]
enum RetryState<F> {
    NotStarted,
    WaitingForFuture(#[pin] F),

    #[cfg(feature = "tokio-1")]
    TimerActive(#[pin] tokio::time::Sleep),

    #[cfg(feature = "tokio-02")]
    TimerActive(#[pin] tokio::time::Delay),
}

impl<F, Fut, B, T, E, OnRetryT> Future for RetryFuture<F, Fut, B, OnRetryT>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: fmt::Display,
    B: BackoffStrategy<E>,
    B::Output: Into<RetryPolicy>,
    OnRetryT: OnRetry<E>,
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
                            if let Some(on_retry) = &mut this.config.on_retry {
                                tokio::spawn(on_retry.on_retry(*this.attempt, None, &error));
                            }

                            return Poll::Ready(Err(error));
                        } else {
                            *this.attempt += 1;
                            *this.attempts_remaining -= 1;

                            let delay: RetryPolicy = this
                                .config
                                .backoff_strategy
                                .delay(*this.attempt, &error)
                                .into();
                            let mut delay_duration = match delay {
                                RetryPolicy::Delay(duration) => duration,
                                RetryPolicy::Break => {
                                    if let Some(on_retry) = &mut this.config.on_retry {
                                        tokio::spawn(on_retry.on_retry(
                                            *this.attempt,
                                            None,
                                            &error,
                                        ));
                                    }

                                    return Poll::Ready(Err(error));
                                }
                            };

                            if let Some(max_delay) = this.config.max_delay {
                                delay_duration = delay_duration.min(max_delay);
                            }

                            if let Some(on_retry) = &mut this.config.on_retry {
                                tokio::spawn(on_retry.on_retry(
                                    *this.attempt,
                                    Some(delay_duration),
                                    &error,
                                ));
                            }

                            #[cfg(feature = "tokio-1")]
                            let delay = tokio::time::sleep(delay_duration);

                            #[cfg(feature = "tokio-02")]
                            let delay = tokio::time::delay_for(delay_duration);

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

/// Trait allowing you to run some future when a retry occurs. Could for example to be used for
/// logging or other kinds of telemetry.
///
/// You wont have to implement this trait manually. It is implemented for functions with the right
/// signature. See [`RetryFuture::on_retry`](struct.RetryFuture.html#method.on_retry) for more details.
pub trait OnRetry<E> {
    /// The type of the future you want to run.
    type Future: 'static + Future<Output = Self::Output> + Send;

    /// The output type of your future.
    type Output: 'static + Send;

    /// Create another future to run.
    ///
    /// If `next_delay` is `None` then your future is out of retries and wont be called again.
    fn on_retry(
        &mut self,
        attempt: u32,
        next_delay: Option<Duration>,
        previous_error: &E,
    ) -> Self::Future;
}

/// A sentinel value that represents doing nothing in between retries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NoOnRetry {
    _cannot_exist: Infallible,
}

impl<E> OnRetry<E> for NoOnRetry {
    type Future = Ready<Infallible>;
    type Output = Infallible;

    #[inline]
    fn on_retry(&mut self, _: u32, _: Option<Duration>, _: &E) -> Self::Future {
        // this is safe because `NoOnRetry` contains an `Infallible` so it cannot be created
        unreachable!()
    }
}

impl<F, E, FutureT> OnRetry<E> for F
where
    F: FnMut(u32, Option<Duration>, &E) -> FutureT,
    FutureT: Future + Send + 'static,
    FutureT::Output: Send + 'static,
{
    type Output = FutureT::Output;
    type Future = FutureT;

    #[inline]
    fn on_retry(
        &mut self,
        attempts: u32,
        next_delay: Option<Duration>,
        previous_error: &E,
    ) -> Self::Future {
        self(attempts, next_delay, previous_error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
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

    #[tokio::test]
    async fn retry_hook_succeed() {
        use std::sync::Arc;
        use tokio::sync::Mutex;

        let errors = Arc::new(Mutex::new(Vec::new()));

        retry_fn(|| async { Err::<Infallible, String>("error".to_string()) })
            .retries(10)
            .on_retry(|attempt, next_delay, error| {
                let errors = Arc::clone(&errors);
                let error = error.clone();
                async move {
                    errors.lock().await.push((attempt, next_delay, error));
                }
            })
            .await
            .unwrap_err();

        let errors = errors.lock().await;
        assert_eq!(errors.len(), 10);
        for n in 1_u32..=10 {
            assert_eq!(
                &errors[(n - 1) as usize],
                &(n, Some(Duration::new(0, 0)), "error".to_string())
            );
        }
    }

    #[tokio::test]
    async fn reusing_the_config() {
        let counter = Arc::new(AtomicUsize::new(0));

        let config = RetryFutureConfig::new(10)
            .max_delay(Duration::from_secs(1))
            .linear_backoff(Duration::from_millis(10))
            .on_retry(|_, _, _| {
                let counter = Arc::clone(&counter);
                async move {
                    counter.fetch_add(1, Ordering::SeqCst);
                }
            });

        let ok_value = retry_fn(|| async { Ok::<_, &str>(true) })
            .with_config(config)
            .await
            .unwrap();
        assert!(ok_value);
        assert_eq!(counter.load(Ordering::SeqCst), 0);

        let err_value = retry_fn(|| async { Err::<(), _>("foo") })
            .with_config(config)
            .await
            .unwrap_err();
        assert_eq!(err_value, "foo");
        assert_eq!(counter.load(Ordering::SeqCst), 10);
    }
}
