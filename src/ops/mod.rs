//! Module of operations that can be performed in a segment tree.
//!
//! A segment tree needs some operation, and this module contains the main [`Operation`] trait,
//! together with the marker trait [`CommutativeOperation`]. This module also contains
//! implementations for simple operations.
//!
//! [`Operation`]: trait.Operation.html
//! [`CommutativeOperation`]: trait.CommutativeOperation.html

use std::cmp;
use std::marker::PhantomData;
use std::num::Wrapping;

#[cfg(feature = "num-ops")]
mod num;

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
/// Each node contains the product of the interval it represents.
pub struct Mul;
/// Each node contains the bitwise xor of the interval it represents.
pub struct Xor;
/// Each node contains the bitwise and of the interval it represents.
pub struct And;
/// Each node contains the bitwise or of the interval it represents.
pub struct Or;

macro_rules! impl_primitive_op {
    ($op:ty, $t:ty, $add:tt, $sub:tt, $iden:expr) => {
        impl Operation<$t> for $op {
            fn combine(a: &$t, b: &$t) -> $t {
                *a $add *b
            }
        }
        impl CommutativeOperation<$t> for $op {}
        impl Identity<$t> for $op {
            fn identity() -> $t {
                ($iden) as $t
            }
        }
        impl Inverse<$t> for $op {
            fn uncombine(a: &mut $t, b: &$t) {
                *a = *a $sub *b;
            }
        }
    };
}
macro_rules! impl_primitive_op_wrapping {
    ($op:ty, $t:ty, $add:tt, $sub:tt, $iden:expr) => {
        impl Operation<Wrapping<$t>> for $op {
            fn combine(a: &Wrapping<$t>, b: &Wrapping<$t>) -> Wrapping<$t> {
                *a $add *b
            }
        }
        impl CommutativeOperation<Wrapping<$t>> for $op {}
        impl Identity<Wrapping<$t>> for $op {
            fn identity() -> Wrapping<$t> {
                Wrapping(($iden) as $t)
            }
        }
        impl Inverse<Wrapping<$t>> for $op {
            fn uncombine(a: &mut Wrapping<$t>, b: &Wrapping<$t>) {
                *a = *a $sub *b;
            }
        }
    }
}
macro_rules! impl_primitive {
    ($t:ty) => {
        impl_primitive_op!(Add, $t, +, -, 0);
        impl_primitive_op!(Mul, $t, *, /, 1);
        impl_primitive_op!(Xor, $t, ^, ^, 0);
        impl_primitive_op!(And, $t, ^, ^, 0);
        impl_primitive_op!(Or, $t, ^, ^, 0);
        impl_primitive_op_wrapping!(Add, $t, +, -, 0);
        impl_primitive_op_wrapping!(Mul, $t, *, /, 1);
        impl_primitive_op_wrapping!(Xor, $t, +, -, 0);
        impl_primitive_op_wrapping!(And, $t, *, /, 1);
        impl_primitive_op_wrapping!(Or, $t, *, /, 1);
    }
}
impl_primitive!(u8);
impl_primitive!(u16);
impl_primitive!(u32);
impl_primitive!(u64);
impl_primitive!(i8);
impl_primitive!(i16);
impl_primitive!(i32);
impl_primitive!(i64);
impl_primitive!(usize);
impl_primitive!(isize);
impl_primitive_op!(Add, f32, +, -, 0);
impl_primitive_op!(Mul, f32, *, /, 1);
impl_primitive_op!(Add, f64, +, -, 0);
impl_primitive_op!(Mul, f64, *, /, 1);

/// Each node contains the maximum value in the interval it represents.
pub struct Max;
/// Each node contains the minimum value in the interval it represents.
pub struct Min;

macro_rules! impl_cmp_primitive_aux {
    ($t:ty, $cmpt:ty, $cmp:tt, $iden:expr) => {
        impl Operation<$t> for $cmpt {
            #[inline(always)]
            fn combine(a: &$t, b: &$t) -> $t {
                cmp::$cmp(*a, *b)
            }
        }
        impl CommutativeOperation<$t> for $cmpt {}
        impl Identity<$t> for $cmpt {
            fn identity() -> $t {
                $iden
            }
        }
    }
}
macro_rules! impl_cmp_primitive {
    ($t:tt) => {
        impl_cmp_primitive_aux!($t, Max, max, ::std::$t::MIN);
        impl_cmp_primitive_aux!($t, Min, min, ::std::$t::MAX);
    }
}
impl_cmp_primitive!(u8);
impl_cmp_primitive!(u16);
impl_cmp_primitive!(u32);
impl_cmp_primitive!(u64);
impl_cmp_primitive!(i8);
impl_cmp_primitive!(i16);
impl_cmp_primitive!(i32);
impl_cmp_primitive!(i64);
impl_cmp_primitive!(usize);
impl_cmp_primitive!(isize);

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
    use std::{f32, i32};
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
    #[test]
    fn ops_and() {
        for i in -200i32 .. 201i32 {
            assert_eq!(And::combine_both(i, And::identity()), i);
        }
        assert_eq!(And::combine_both(i32::MAX, And::identity()), i32::MAX);
        assert_eq!(And::combine_both(i32::MIN, And::identity()), i32::MIN);
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
