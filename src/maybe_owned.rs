//! This module contains a variant of [`Cow`] that doesn't require [`Clone`].
//!
//! [`Cow`]: https://doc.rust-lang.org/std/borrow/enum.Cow.html
//! [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html

use std::cmp;
use std::fmt::{self, Debug, Display, Formatter};
use std::default::Default;
use std::hash::{Hash, Hasher};

/// A variant of [`Cow`] that doesn't require [`Clone`].
///
/// [`Cow`]: https://doc.rust-lang.org/std/borrow/enum.Cow.html
/// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
pub enum MaybeOwned<'a, T: 'a> {
    Borrowed(&'a T),
    Owned(T)
}

impl<'a, T: 'a> MaybeOwned<'a, T> {
    /// Get a reference to the contained value.
    #[inline]
    pub fn as_ref<'b>(&'b self) -> &'b T where 'b: 'a {
        match *self {
            MaybeOwned::Borrowed(v) => v,
            MaybeOwned::Owned(ref v) => &v
        }
    }
}
impl<'a, T: 'a + Clone> MaybeOwned<'a, T> {
    /// Get the value, cloning if necessary.
    #[inline]
    pub fn get_or_clone(self) -> T {
        match self {
            MaybeOwned::Borrowed(v) => v.clone(),
            MaybeOwned::Owned(v) => v
        }
    }
}

impl<'a, T: 'a + Debug> Debug for MaybeOwned<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            MaybeOwned::Borrowed(v)  => write!(f, "Borrw({:?})", v),
            MaybeOwned::Owned(ref v) => write!(f, "Owned({:?})", v)
        }
    }
}

impl<'a, T: 'a + Display> Display for MaybeOwned<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            MaybeOwned::Borrowed(v)  => write!(f, "Borrw({})", v),
            MaybeOwned::Owned(ref v) => write!(f, "Owned({})", v)
        }
    }
}

impl<'a, T: 'a + PartialEq> cmp::PartialEq for MaybeOwned<'a, T> {
    #[inline]
    fn eq(&self, other: &MaybeOwned<T>) -> bool {
        self.as_ref().eq(other.as_ref())
    }
    #[inline]
    fn ne(&self, other: &MaybeOwned<T>) -> bool {
        self.as_ref().ne(other.as_ref())
    }
}
impl<'a, T: 'a + Eq> cmp::Eq for MaybeOwned<'a, T> { }

impl<'a, T: 'a + PartialOrd> cmp::PartialOrd for MaybeOwned<'a, T> {
    #[inline]
    fn partial_cmp(&self, other: &MaybeOwned<T>) -> Option<cmp::Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
    #[inline]
    fn lt(&self, other: &MaybeOwned<T>) -> bool {
        self.as_ref().lt(other.as_ref())
    }
    #[inline]
    fn le(&self, other: &MaybeOwned<T>) -> bool {
        self.as_ref().le(other.as_ref())
    }
    #[inline]
    fn gt(&self, other: &MaybeOwned<T>) -> bool {
        self.as_ref().gt(other.as_ref())
    }
    #[inline]
    fn ge(&self, other: &MaybeOwned<T>) -> bool {
        self.as_ref().ge(other.as_ref())
    }
}
impl<'a, T: 'a + Ord> cmp::Ord for MaybeOwned<'a, T> {
    #[inline]
    fn cmp(&self, other: &MaybeOwned<T>) -> cmp::Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl<'a, T: 'a + Default> Default for MaybeOwned<'a, T> {
    #[inline]
    fn default() -> MaybeOwned<'a, T> {
        MaybeOwned::Owned(Default::default())
    }
}

impl<'a, T: 'a + Hash> Hash for MaybeOwned<'a, T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state)
    }
}
