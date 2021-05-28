use futures::future::{BoxFuture, Ready};
use std::{convert::Infallible, fmt, future::Future, sync::Arc, time::Duration};

/// Trait allowing you to run some future when a retry occurs. Could for example to be used for
/// logging or other kinds of telemetry.
///
/// You wont have to implement this trait manually. It is implemented for functions with the right
/// signature. See [`RetryFuture::on_retry`](struct.RetryFuture.html#method.on_retry) for more details.
pub trait OnRetry<E> {
    /// The type of the future you want to run.
    type Future: 'static + Future<Output = ()> + Send;

    /// Create another future to run.
    ///
    /// If `next_delay` is `None` then your future is out of retries and wont be called again.
    fn on_retry(
        &self,
        attempt: u32,
        next_delay: Option<Duration>,
        previous_error: &E,
    ) -> Self::Future;
}

/// A sentinel value that represents doing nothing in between retries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NoOnRetry {
    cannot_exist: Infallible,
}

impl<E> OnRetry<E> for NoOnRetry {
    type Future = Ready<()>;

    #[inline]
    fn on_retry(&self, _: u32, _: Option<Duration>, _: &E) -> Self::Future {
        match self.cannot_exist {}
    }
}

impl<F, E, FutureT> OnRetry<E> for F
where
    F: Fn(u32, Option<Duration>, &E) -> FutureT,
    FutureT: Future<Output = ()> + Send + 'static,
    FutureT::Output: Send + 'static,
{
    type Future = FutureT;

    #[inline]
    fn on_retry(
        &self,
        attempts: u32,
        next_delay: Option<Duration>,
        previous_error: &E,
    ) -> Self::Future {
        self(attempts, next_delay, previous_error)
    }
}

/// A boxed [`OnRetry`] trait object.
///
/// Created via [`RetryFutureConfig::boxed_on_retry`].
///
/// [`RetryFutureConfig::boxed_on_retry`]: crate::RetryFutureConfig::boxed_on_retry
pub struct BoxOnRetry<E> {
    inner: Arc<dyn OnRetry<E, Future = BoxFuture<'static, ()>>>,
}

impl<E> Clone for BoxOnRetry<E> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<E> fmt::Debug for BoxOnRetry<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BoxOnRetry").finish()
    }
}

// On `OnRetry` adapter that boxes the future
struct BoxOnRetryFuture<T>(T);

impl<T, E> OnRetry<E> for BoxOnRetryFuture<T>
where
    T: OnRetry<E>,
{
    type Future = BoxFuture<'static, ()>;

    fn on_retry(
        &self,
        attempt: u32,
        next_delay: Option<Duration>,
        previous_error: &E,
    ) -> Self::Future {
        Box::pin(self.0.on_retry(attempt, next_delay, previous_error))
    }
}

impl<E> BoxOnRetry<E> {
    pub(crate) fn new<T>(inner: T) -> Self
    where
        T: OnRetry<E> + 'static,
        T::Future: Send + Sync + 'static,
    {
        Self {
            inner: Arc::new(BoxOnRetryFuture(inner)),
        }
    }
}

impl<E> OnRetry<E> for BoxOnRetry<E> {
    type Future = BoxFuture<'static, ()>;

    fn on_retry(
        &self,
        attempt: u32,
        next_delay: Option<Duration>,
        previous_error: &E,
    ) -> Self::Future {
        self.inner.on_retry(attempt, next_delay, previous_error)
    }
}
