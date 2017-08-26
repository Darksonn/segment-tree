//! Module of operations that can be performed in a segment tree.
//!
//! A segment tree needs some operation, and this module contains the main [`Operation`] trait,
//! together with the marker trait [`CommutativeOperation`]. This module also contains
//! implementations for simple operations.
//!
//! [`Operation`]: trait.Operation.html
//! [`CommutativeOperation`]: trait.CommutativeOperation.html

use std::{cmp, ops};
use std::marker::PhantomData;
use std::num::Wrapping;

/// A trait that specifies which associative operator to use in a segment tree.
pub trait Operation<N> {
    /// The operation that is performed to combine two intervals in the segment tree.
    ///
    /// This function must be associative, that is `combine(combine(a, b), c) = combine(a,
    /// combine(b, c))`.
    fn combine(a: &N, b: &N) -> N;
    /// Replace the value in a with `combine(a, b)`. This function exists to allow certain
    /// optimizations and by default simply calls `combine`.
    #[inline]
    fn combine_mut(a: &mut N, b: &N) {
        let res = Self::combine(&*a, b);
        *a = res;
    }
    /// Replace the value in a with `combine(a, b)`. This function exists to allow certain
    /// optimizations and by default simply calls `combine`.
    #[inline]
    fn combine_mut2(a: &N, b: &mut N) {
        let res = Self::combine(a, &*b);
        *b = res;
    }
    /// Must return the same as `combine`. This function exists to allow certain optimizations
    /// and by default simply calls `combine_mut`.
    #[inline]
    fn combine_left(mut a: N, b: &N) -> N {
        Self::combine_mut(&mut a, b); a
    }
    /// Must return the same as `combine`. This function exists to allow certain optimizations
    /// and by default simply calls `combine_mut2`.
    #[inline]
    fn combine_right(a: &N, mut b: N) -> N {
        Self::combine_mut2(a, &mut b); b
    }
    /// Must return the same as `combine`. This function exists to allow certain optimizations
    /// and by default simply calls `combine_left`.
    #[inline]
    fn combine_both(a: N, b: N) -> N {
        Self::combine_left(a, &b)
    }
}

/// A marker trait that specifies that an [`Operation`] is commutative, that is: `combine(a, b) = combine(b, a)`.
///
/// [`Operation`]: trait.Operation.html
pub trait CommutativeOperation<N>: Operation<N> {}

/// A trait that specifies that this type has an identity under this operation.
///
/// An identity must satisfy `combine(a, id) = a` and `combine(id, a) = a`.
pub trait Identity<N> {
    /// Returns any identity.
    fn identity() -> N;
}

/// A trait that specifies that this type allows uncombining.
pub trait Inverse<N> {
    /// Returns some value such that `combine(uncombine(a, b), b) = a`.
    fn uncombine(a: &mut N, b: &N);
}

/// Each node contains the sum of the interval it represents.
pub struct Add;
impl<T: ops::Add<Output=T> + Copy> Operation<T> for Add {
    #[inline(always)]
    fn combine(a: &T, b: &T) -> T {
        *a + *b
    }
}
impl<T: ops::Sub<Output=T> + Copy> Inverse<T> for Add {
    #[inline(always)]
    fn uncombine(a: &mut T, b: &T) {
        *a = *a - *b
    }
}
impl<T: ops::Add<Output=T> + Copy> CommutativeOperation<T> for Add {}
impl Identity<u8> for Add { fn identity() -> u8 { 0 } }
impl Identity<u16> for Add { fn identity() -> u16 { 0 } }
impl Identity<u32> for Add { fn identity() -> u32 { 0 } }
impl Identity<u64> for Add { fn identity() -> u64 { 0 } }
impl Identity<i8> for Add { fn identity() -> i8 { 0 } }
impl Identity<i16> for Add { fn identity() -> i16 { 0 } }
impl Identity<i32> for Add { fn identity() -> i32 { 0 } }
impl Identity<i64> for Add { fn identity() -> i64 { 0 } }
impl Identity<f32> for Add { fn identity() -> f32 { 0.0 } }
impl Identity<f64> for Add { fn identity() -> f64 { 0.0 } }
impl Identity<usize> for Add { fn identity() -> usize { 0 } }
impl Identity<isize> for Add { fn identity() -> isize { 0 } }
impl<T> Identity<Wrapping<T>> for Add where Add: Identity<T> {
    fn identity() -> Wrapping<T> {
        Wrapping(Self::identity())
    }
}

/// Each node contains the product of the interval it represents.
pub struct Mul;
impl<T: ops::Mul<Output=T> + Copy> Operation<T> for Mul {
    #[inline(always)]
    fn combine(a: &T, b: &T) -> T {
        *a * *b
    }
}
impl<T: ops::Div<Output=T> + Copy> Inverse<T> for Mul {
    #[inline(always)]
    fn uncombine(a: &mut T, b: &T) {
        *a = *a / *b
    }
}
impl CommutativeOperation<u8> for Mul {}
impl CommutativeOperation<u16> for Mul {}
impl CommutativeOperation<u32> for Mul {}
impl CommutativeOperation<u64> for Mul {}
impl CommutativeOperation<i8> for Mul {}
impl CommutativeOperation<i16> for Mul {}
impl CommutativeOperation<i32> for Mul {}
impl CommutativeOperation<i64> for Mul {}
impl CommutativeOperation<usize> for Mul {}
impl CommutativeOperation<isize> for Mul {}
impl CommutativeOperation<f32> for Mul {}
impl CommutativeOperation<f64> for Mul {}
impl<T: Copy> CommutativeOperation<Wrapping<T>> for Mul where Mul: CommutativeOperation<T>, Wrapping<T>: ops::Mul<Output=Wrapping<T>> {}
impl Identity<u8> for Mul { fn identity() -> u8 { 1 } }
impl Identity<u16> for Mul { fn identity() -> u16 { 1 } }
impl Identity<u32> for Mul { fn identity() -> u32 { 1 } }
impl Identity<u64> for Mul { fn identity() -> u64 { 1 } }
impl Identity<i8> for Mul { fn identity() -> i8 { 1 } }
impl Identity<i16> for Mul { fn identity() -> i16 { 1 } }
impl Identity<i32> for Mul { fn identity() -> i32 { 1 } }
impl Identity<i64> for Mul { fn identity() -> i64 { 1 } }
impl Identity<f32> for Mul { fn identity() -> f32 { 1.0 } }
impl Identity<f64> for Mul { fn identity() -> f64 { 1.0 } }
impl Identity<usize> for Mul { fn identity() -> usize { 1 } }
impl Identity<isize> for Mul { fn identity() -> isize { 1 } }
impl<T> Identity<Wrapping<T>> for Mul where Mul: Identity<T> {
    fn identity() -> Wrapping<T> {
        Wrapping(Self::identity())
    }
}


/// Each node contains the bitwise xor of the interval it represents.
pub struct Xor;
impl<T: ops::BitXor<Output=T> + Copy> Operation<T> for Xor {
    #[inline(always)]
    fn combine(a: &T, b: &T) -> T {
        *a ^ *b
    }
}
impl<T: ops::BitXor<Output=T> + Copy> Inverse<T> for Xor {
    #[inline(always)]
    fn uncombine(a: &mut T, b: &T) {
        *a = *a ^ *b
    }
}
impl CommutativeOperation<u8> for Xor {}
impl CommutativeOperation<u16> for Xor {}
impl CommutativeOperation<u32> for Xor {}
impl CommutativeOperation<u64> for Xor {}
impl CommutativeOperation<i8> for Xor {}
impl CommutativeOperation<i16> for Xor {}
impl CommutativeOperation<i32> for Xor {}
impl CommutativeOperation<i64> for Xor {}
impl CommutativeOperation<usize> for Xor {}
impl CommutativeOperation<isize> for Xor {}
impl<T: Copy> CommutativeOperation<Wrapping<T>> for Xor where Xor: CommutativeOperation<T>, Wrapping<T>: ops::BitXor<Output=Wrapping<T>> {}
impl Identity<u8> for Xor { fn identity() -> u8 { 0 } }
impl Identity<u16> for Xor { fn identity() -> u16 { 0 } }
impl Identity<u32> for Xor { fn identity() -> u32 { 0 } }
impl Identity<u64> for Xor { fn identity() -> u64 { 0 } }
impl Identity<i8> for Xor { fn identity() -> i8 { 0 } }
impl Identity<i16> for Xor { fn identity() -> i16 { 0 } }
impl Identity<i32> for Xor { fn identity() -> i32 { 0 } }
impl Identity<i64> for Xor { fn identity() -> i64 { 0 } }
impl Identity<usize> for Xor { fn identity() -> usize { 0 } }
impl Identity<isize> for Xor { fn identity() -> isize { 0 } }
impl<T> Identity<Wrapping<T>> for Xor where Xor: Identity<T> {
    fn identity() -> Wrapping<T> {
        Wrapping(Self::identity())
    }
}

/// Each node contains the bitwise and of the interval it represents.
pub struct And;
impl<T: ops::BitAnd<Output=T> + Copy> Operation<T> for And {
    #[inline(always)]
    fn combine(a: &T, b: &T) -> T {
        *a & *b
    }
}
impl CommutativeOperation<u8> for And {}
impl CommutativeOperation<u16> for And {}
impl CommutativeOperation<u32> for And {}
impl CommutativeOperation<u64> for And {}
impl CommutativeOperation<i8> for And {}
impl CommutativeOperation<i16> for And {}
impl CommutativeOperation<i32> for And {}
impl CommutativeOperation<i64> for And {}
impl CommutativeOperation<usize> for And {}
impl CommutativeOperation<isize> for And {}
impl<T: Copy> CommutativeOperation<Wrapping<T>> for And where And: CommutativeOperation<T>, Wrapping<T>: ops::BitAnd<Output=Wrapping<T>> {}
impl Identity<u8> for And { fn identity() -> u8 { !0 } }
impl Identity<u16> for And { fn identity() -> u16 { !0 } }
impl Identity<u32> for And { fn identity() -> u32 { !0 } }
impl Identity<u64> for And { fn identity() -> u64 { !0 } }
impl Identity<i8> for And { fn identity() -> i8 { !0 } }
impl Identity<i16> for And { fn identity() -> i16 { !0 } }
impl Identity<i32> for And { fn identity() -> i32 { !0 } }
impl Identity<i64> for And { fn identity() -> i64 { !0 } }
impl Identity<usize> for And { fn identity() -> usize { !0 } }
impl Identity<isize> for And { fn identity() -> isize { !0 } }
impl<T> Identity<Wrapping<T>> for And where And: Identity<T> {
    fn identity() -> Wrapping<T> {
        Wrapping(Self::identity())
    }
}

/// Each node contains the bitwise or of the interval it represents.
pub struct Or;
impl<T: ops::BitOr<Output=T> + Copy> Operation<T> for Or {
    #[inline(always)]
    fn combine(a: &T, b: &T) -> T {
        *a | *b
    }
}
impl CommutativeOperation<u8> for Or {}
impl CommutativeOperation<u16> for Or {}
impl CommutativeOperation<u32> for Or {}
impl CommutativeOperation<u64> for Or {}
impl CommutativeOperation<i8> for Or {}
impl CommutativeOperation<i16> for Or {}
impl CommutativeOperation<i32> for Or {}
impl CommutativeOperation<i64> for Or {}
impl CommutativeOperation<usize> for Or {}
impl CommutativeOperation<isize> for Or {}
impl<T: Copy> CommutativeOperation<Wrapping<T>> for Or where Or: CommutativeOperation<T>, Wrapping<T>: ops::BitOr<Output=Wrapping<T>> {}
impl Identity<u8> for Or { fn identity() -> u8 { 0 } }
impl Identity<u16> for Or { fn identity() -> u16 { 0 } }
impl Identity<u32> for Or { fn identity() -> u32 { 0 } }
impl Identity<u64> for Or { fn identity() -> u64 { 0 } }
impl Identity<i8> for Or { fn identity() -> i8 { 0 } }
impl Identity<i16> for Or { fn identity() -> i16 { 0 } }
impl Identity<i32> for Or { fn identity() -> i32 { 0 } }
impl Identity<i64> for Or { fn identity() -> i64 { 0 } }
impl Identity<usize> for Or { fn identity() -> usize { 0 } }
impl Identity<isize> for Or { fn identity() -> isize { 0 } }
impl<T> Identity<Wrapping<T>> for Or where Or: Identity<T> {
    fn identity() -> Wrapping<T> {
        Wrapping(Self::identity())
    }
}

/// Each node contains the maximum value in the interval it represents.
pub struct Max;
impl<T: cmp::Ord + Copy> Operation<T> for Max {
    #[inline(always)]
    fn combine(a: &T, b: &T) -> T {
        cmp::max(*a, *b)
    }
}
impl<T: cmp::Ord + Copy> CommutativeOperation<T> for Max {}
impl Identity<u8>  for Max { fn identity() -> u8  { ::std::u8::MIN  } }
impl Identity<u16> for Max { fn identity() -> u16 { ::std::u16::MIN } }
impl Identity<u32> for Max { fn identity() -> u32 { ::std::u32::MIN } }
impl Identity<u64> for Max { fn identity() -> u64 { ::std::u64::MIN } }
impl Identity<i8>  for Max { fn identity() -> i8  { ::std::i8::MIN  } }
impl Identity<i16> for Max { fn identity() -> i16 { ::std::i16::MIN } }
impl Identity<i32> for Max { fn identity() -> i32 { ::std::i32::MIN } }
impl Identity<i64> for Max { fn identity() -> i64 { ::std::i64::MIN } }
impl Identity<usize> for Max { fn identity() -> usize { ::std::usize::MIN } }
impl Identity<isize> for Max { fn identity() -> isize { ::std::isize::MIN } }
impl<T> Identity<Wrapping<T>> for Max where Max: Identity<T> {
    fn identity() -> Wrapping<T> {
        Wrapping(Self::identity())
    }
}

/// Variant of [`Max`] that considers NaN smaller than anything.
///
/// [`Max`]: struct.Max.html
pub struct MaxIgnoreNaN;
impl Operation<f32> for MaxIgnoreNaN {
    #[inline(always)]
    fn combine(a: &f32, b: &f32) -> f32 {
        if b > a || a.is_nan() { *b } else { *a }
    }
}
impl Operation<f64> for MaxIgnoreNaN {
    #[inline(always)]
    fn combine(a: &f64, b: &f64) -> f64 {
        if b > a || a.is_nan() { *b } else { *a }
    }
}
impl Identity<f32> for MaxIgnoreNaN { fn identity() -> f32 { ::std::f32::NAN } }
impl Identity<f64> for MaxIgnoreNaN { fn identity() -> f64 { ::std::f64::NAN } }

/// Variant of [`Max`] that considers NaN larger than anything.
///
/// [`Max`]: struct.Max.html
pub struct MaxTakeNaN;
impl Operation<f32> for MaxTakeNaN {
    #[inline(always)]
    fn combine(a: &f32, b: &f32) -> f32 {
        if b > a || b.is_nan() { *b } else { *a }
    }
}
impl Operation<f64> for MaxTakeNaN {
    #[inline(always)]
    fn combine(a: &f64, b: &f64) -> f64 {
        if b > a || b.is_nan() { *b } else { *a }
    }
}
impl Identity<f32> for MaxTakeNaN { fn identity() -> f32 { ::std::f32::NEG_INFINITY } }
impl Identity<f64> for MaxTakeNaN { fn identity() -> f64 { ::std::f64::NEG_INFINITY } }

/// Each node contains the minimum value in the interval it represents.
pub struct Min;
impl<T: cmp::Ord + Copy> Operation<T> for Min {
    #[inline(always)]
    fn combine(a: &T, b: &T) -> T {
        cmp::min(*a, *b)
    }
}
impl<T: cmp::Ord + Copy> CommutativeOperation<T> for Min {}
impl Identity<u8>  for Min { fn identity() -> u8  { ::std::u8::MAX  } }
impl Identity<u16> for Min { fn identity() -> u16 { ::std::u16::MAX } }
impl Identity<u32> for Min { fn identity() -> u32 { ::std::u32::MAX } }
impl Identity<u64> for Min { fn identity() -> u64 { ::std::u64::MAX } }
impl Identity<i8>  for Min { fn identity() -> i8  { ::std::i8::MAX  } }
impl Identity<i16> for Min { fn identity() -> i16 { ::std::i16::MAX } }
impl Identity<i32> for Min { fn identity() -> i32 { ::std::i32::MAX } }
impl Identity<i64> for Min { fn identity() -> i64 { ::std::i64::MAX } }
impl Identity<usize> for Min { fn identity() -> usize { ::std::usize::MAX } }
impl Identity<isize> for Min { fn identity() -> isize { ::std::isize::MAX } }
impl<T> Identity<Wrapping<T>> for Min where Min: Identity<T> {
    fn identity() -> Wrapping<T> {
        Wrapping(Self::identity())
    }
}

/// Variant of [`Min`] that considers NaN larger than anything.
///
/// [`Min`]: struct.Min.html
pub struct MinIgnoreNaN;
impl Operation<f32> for MinIgnoreNaN {
    #[inline(always)]
    fn combine(a: &f32, b: &f32) -> f32 {
        if b > a || b.is_nan() { *a } else { *b }
    }
}
impl Operation<f64> for MinIgnoreNaN {
    #[inline(always)]
    fn combine(a: &f64, b: &f64) -> f64 {
        if b > a || b.is_nan() { *a } else { *b }
    }
}
impl Identity<f32> for MinIgnoreNaN { fn identity() -> f32 { ::std::f32::NAN } }
impl Identity<f64> for MinIgnoreNaN { fn identity() -> f64 { ::std::f64::NAN } }

/// Variant of [`Min`] that considers NaN smaller than anything.
///
/// [`Min`]: struct.Min.html
pub struct MinTakeNaN;
impl Operation<f32> for MinTakeNaN {
    #[inline(always)]
    fn combine(a: &f32, b: &f32) -> f32 {
        if b > a || a.is_nan() { *a } else { *b }
    }
}
impl Operation<f64> for MinTakeNaN {
    #[inline(always)]
    fn combine(a: &f64, b: &f64) -> f64 {
        if b > a || a.is_nan() { *a } else { *b }
    }
}
impl Identity<f32> for MinTakeNaN { fn identity() -> f32 { ::std::f32::INFINITY } }
impl Identity<f64> for MinTakeNaN { fn identity() -> f64 { ::std::f64::INFINITY } }

#[cfg(test)]
mod tests {
    use std::f32;
    use ops::*;
    #[test]
    fn ops_nan() {
        assert_eq!(MaxIgnoreNaN::combine_both(0.0, 1.0), 1.0);
        assert_eq!(MaxIgnoreNaN::combine_both(1.0, 0.0), 1.0);
        assert_eq!(MaxIgnoreNaN::combine_both(f32::NAN, 1.0), 1.0);
        assert_eq!(MaxIgnoreNaN::combine_both(1.0, f32::NAN), 1.0);
        assert_eq!(MaxIgnoreNaN::combine_both(f32::NAN, f32::NEG_INFINITY), f32::NEG_INFINITY);
        assert_eq!(MaxIgnoreNaN::combine_both(f32::NEG_INFINITY, f32::NAN), f32::NEG_INFINITY);
        assert!(MaxIgnoreNaN::combine_both(f32::NAN, f32::NAN).is_nan());

        assert_eq!(MinIgnoreNaN::combine_both(0.0, 1.0), 0.0);
        assert_eq!(MinIgnoreNaN::combine_both(1.0, 0.0), 0.0);
        assert_eq!(MinIgnoreNaN::combine_both(f32::NAN, 1.0), 1.0);
        assert_eq!(MinIgnoreNaN::combine_both(1.0, f32::NAN), 1.0);
        assert_eq!(MinIgnoreNaN::combine_both(f32::NAN, f32::INFINITY), f32::INFINITY);
        assert_eq!(MinIgnoreNaN::combine_both(f32::INFINITY, f32::NAN), f32::INFINITY);
        assert!(MinIgnoreNaN::combine_both(f32::NAN, f32::NAN).is_nan());

        assert_eq!(MaxTakeNaN::combine_both(0.0, 1.0), 1.0);
        assert_eq!(MaxTakeNaN::combine_both(1.0, 0.0), 1.0);
        assert!(MaxTakeNaN::combine_both(f32::NAN, f32::INFINITY).is_nan());
        assert!(MaxTakeNaN::combine_both(f32::INFINITY, f32::NAN).is_nan());
        assert!(MaxTakeNaN::combine_both(f32::NAN, f32::NEG_INFINITY).is_nan());
        assert!(MaxTakeNaN::combine_both(f32::NEG_INFINITY, f32::NAN).is_nan());
        assert!(MaxTakeNaN::combine_both(f32::NAN, f32::NAN).is_nan());

        assert_eq!(MinTakeNaN::combine_both(0.0, 1.0), 0.0);
        assert_eq!(MinTakeNaN::combine_both(1.0, 0.0), 0.0);
        assert!(MinTakeNaN::combine_both(f32::NAN, f32::INFINITY).is_nan());
        assert!(MinTakeNaN::combine_both(f32::INFINITY, f32::NAN).is_nan());
        assert!(MinTakeNaN::combine_both(f32::NAN, f32::NEG_INFINITY).is_nan());
        assert!(MinTakeNaN::combine_both(f32::NEG_INFINITY, f32::NAN).is_nan());
        assert!(MinTakeNaN::combine_both(f32::NAN, f32::NAN).is_nan());
    }
}

/// Store more information in each node.
pub struct Pair<A, B> {
    phantom: PhantomData<(A,B)>
}
impl<TA, TB, A: Operation<TA>, B: Operation<TB>> Operation<(TA, TB)> for Pair<A, B> {
    #[inline]
    fn combine(a: &(TA, TB), b: &(TA, TB)) -> (TA, TB) {
        (A::combine(&a.0, &b.0), B::combine(&a.1, &b.1))
    }
    #[inline]
    fn combine_mut(a: &mut (TA, TB), b: &(TA, TB)) {
        A::combine_mut(&mut a.0, &b.0);
        B::combine_mut(&mut a.1, &b.1);
    }
    #[inline]
    fn combine_mut2(a: &(TA, TB), b: &mut (TA, TB)) {
        A::combine_mut2(&a.0, &mut b.0);
        B::combine_mut2(&a.1, &mut b.1);
    }
    #[inline]
    fn combine_left(a: (TA, TB), b: &(TA, TB)) -> (TA, TB) {
        (A::combine_left(a.0, &b.0), B::combine_left(a.1, &b.1))
    }
    #[inline]
    fn combine_right(a: &(TA, TB), b: (TA, TB)) -> (TA, TB) {
        (A::combine_right(&a.0, b.0), B::combine_right(&a.1, b.1))
    }
    #[inline]
    fn combine_both(a: (TA, TB), b: (TA, TB)) -> (TA, TB) {
        (A::combine_both(a.0, b.0), B::combine_both(a.1, b.1))
    }
}
impl<TA, TB, A: Inverse<TA>, B: Inverse<TB>> Inverse<(TA, TB)> for Pair<A, B> {
    #[inline(always)]
    fn uncombine(a: &mut (TA, TB), b: &(TA, TB)) {
        A::uncombine(&mut a.0, &b.0);
        B::uncombine(&mut a.1, &b.1);
    }
}
impl<TA, TB, A: CommutativeOperation<TA>, B: CommutativeOperation<TB>> CommutativeOperation<(TA, TB)> for Pair<A, B> {}
impl<TA, TB, A: Identity<TA>, B: Identity<TB>> Identity<(TA,TB)> for Pair<A, B> {
    fn identity() -> (TA, TB) {
        (A::identity(), B::identity())
    }
}

/// Adds an identity to an operation by wrapping the type in [`Option`]. Clones when combined with
/// None.
///
/// [`Option`]: https://doc.rust-lang.org/std/option/enum.Option.html
pub struct WithIdentity<A> {
    phantom: PhantomData<A>
}
impl<TA: Clone, A: Operation<TA>> Operation<Option<TA>> for WithIdentity<A> {
    #[inline]
    fn combine(a: &Option<TA>, b: &Option<TA>) -> Option<TA> {
        match *a {
            None => b.as_ref().map(|bb| bb.clone()),
            Some(ref aa) => match *b {
                None => Some(aa.clone()),
                Some(ref bb) => Some(A::combine(aa, bb))
            }
        }
    }
    #[inline]
    fn combine_mut(a: &mut Option<TA>, b: &Option<TA>) {
        match *a {
            None => *a = b.clone(),
            Some(ref mut aa) => match *b {
                None => {}, // no change
                Some(ref bb) => A::combine_mut(aa, bb)
            }
        }
    }
    #[inline]
    fn combine_mut2(a: &Option<TA>, b: &mut Option<TA>) {
        match *a {
            None => {}, // no change
            Some(ref aa) => match *b {
                None => *b = a.clone(),
                Some(ref mut bb) => A::combine_mut2(aa, bb)
            }
        }
    }
    #[inline]
    fn combine_left(a: Option<TA>, b: &Option<TA>) -> Option<TA> {
        match *b {
            None => a,
            Some(ref bb) => match a {
                None => Some(bb.clone()),
                Some(aa) => Some(A::combine_left(aa, bb))
            }
        }
    }
    #[inline]
    fn combine_right(a: &Option<TA>, b: Option<TA>) -> Option<TA> {
        match *a {
            None => b,
            Some(ref aa) => match b {
                None => Some(aa.clone()),
                Some(bb) => Some(A::combine_right(aa, bb))
            }
        }
    }
    #[inline]
    fn combine_both(a: Option<TA>, b: Option<TA>) -> Option<TA> {
        match a {
            None => b,
            Some(aa) => match b {
                None => Some(aa),
                Some(bb) => Some(A::combine_both(aa, bb))
            }
        }
    }
}
impl<TA: Clone, A: CommutativeOperation<TA>> CommutativeOperation<Option<TA>> for WithIdentity<A> {}
impl<TA> Identity<Option<TA>> for WithIdentity<TA> { fn identity() -> Option<TA> { None } }
