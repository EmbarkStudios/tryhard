//! The types of backoff strategies that are supported

use crate::RetryPolicy;
use std::fmt;
use std::time::Duration;

/// Trait for computing the amount of delay between attempts.
pub trait BackoffStrategy<E> {
    /// The delay type. Will normally be either [`Duration`] or [`RetryPolicy`].
    ///
    /// [`Duration`]: https://doc.rust-lang.org/stable/std/time/struct.Duration.html
    /// [`RetryPolicy`]: ../enum.RetryPolicy.html
    type Output;

    /// Compute the amount of delay given the number of attempts so far and the most previous
    /// error.
    fn delay(&mut self, attempt: u32, error: &E) -> Self::Output;
}

/// No backoff. This will make the future be retried immediately without any delay in between
/// attempts.
#[derive(Debug, Clone, Copy)]
pub struct NoBackoff;

impl<E> BackoffStrategy<E> for NoBackoff {
    type Output = Duration;

    #[inline]
    fn delay(&mut self, _attempt: u32, _error: &E) -> Duration {
        Duration::new(0, 0)
    }
}

/// Exponential backoff. The delay will double each time.
#[derive(Debug, Clone, Copy)]
pub struct ExponentialBackoff {
    pub(crate) delay: Duration,
}

impl<E> BackoffStrategy<E> for ExponentialBackoff {
    type Output = Duration;

    #[inline]
    fn delay(&mut self, _attempt: u32, _error: &E) -> Duration {
        let prev_delay = self.delay;
        self.delay *= 2;
        prev_delay
    }
}

/// Fixed backoff. The delay wont change between attempts.
#[derive(Debug, Clone, Copy)]
pub struct FixedBackoff {
    pub(crate) delay: Duration,
}

impl<E> BackoffStrategy<E> for FixedBackoff {
    type Output = Duration;

    #[inline]
    fn delay(&mut self, _attempt: u32, _error: &E) -> Duration {
        self.delay
    }
}

/// Linear backoff. The delay will scale linearly with the number of attempts.
#[derive(Debug, Clone, Copy)]
pub struct LinearBackoff {
    pub(crate) delay: Duration,
}

impl<E> BackoffStrategy<E> for LinearBackoff {
    type Output = Duration;

    #[inline]
    fn delay(&mut self, attempt: u32, _error: &E) -> Duration {
        self.delay * attempt
    }
}

/// A custom backoff strategy defined by a function.
#[derive(Clone, Copy)]
pub struct CustomBackoffStrategy<F> {
    pub(crate) f: F,
}

impl<F, E, T> BackoffStrategy<E> for CustomBackoffStrategy<F>
where
    F: FnMut(u32, &E) -> T,
    T: Into<RetryPolicy>,
{
    type Output = RetryPolicy;

    #[inline]
    fn delay(&mut self, attempt: u32, error: &E) -> RetryPolicy {
        (self.f)(attempt, error).into()
    }
}

impl<F> fmt::Debug for CustomBackoffStrategy<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CustomBackoffStrategy")
            .field("f", &format_args!("<{}>", std::any::type_name::<F>()))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::Infallible;

    #[test]
    fn custom_has_useful_debug_impl() {
        let f = |_: u32, _: Infallible| Duration::from_secs(1);
        let backoff = CustomBackoffStrategy { f };

        assert_eq!(
            format!("{:?}", backoff),
            "CustomBackoffStrategy { f: <tryhard::backoff_strategies::tests::custom_has_useful_debug_impl::{{closure}}> }",
        );
    }
}
