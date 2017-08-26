//! This module requires the `num-ops` feature and supplies implementations for various types from
//! the `num` crate.

use ops::{Operation, CommutativeOperation, Identity, Inverse};
use ops::{Add, Mul, Xor, And, Or};
use num::{BigInt, BigUint, Complex, Zero, One};
use num::bigint::Sign;
use num::integer::Integer;
use num::rational::Ratio;

use std::mem;
use std::num::Wrapping;

macro_rules! impl_operation_for_add_no_addassign {
    ($t:ty) => {
        impl Operation<$t> for Add {
            fn combine(a: &$t, b: &$t) -> $t {
                a.clone() + b
            }
            fn combine_mut(a: &mut $t, b: &$t) {
                let aa = mem::replace(a, Add::identity());
                *a = aa + b;
            }
            fn combine_mut2(a: &$t, b: &mut $t) {
                let bb = mem::replace(b, Add::identity());
                *b = bb + a;
            }
            fn combine_left(a: $t, b: &$t) -> $t {
                a + b
            }
            fn combine_right(a: &$t, b: $t) -> $t {
                b + a
            }
        }
        impl Inverse<$t> for Add {
            fn uncombine(a: &mut $t, b: &$t) {
                let aa = mem::replace(a, Add::identity());
                *a = aa - b;
            }
        }
    }
}

macro_rules! impl_identity_for_add {
    ($t:ty => $iden:expr) => {
        impl Identity<$t> for Add {
            fn identity() -> $t {
                $iden
            }
        }
    }
}

impl_operation_for_add_no_addassign!(BigInt);
impl_identity_for_add!(BigInt => BigInt::from_slice(Sign::NoSign, &[]));
impl CommutativeOperation<BigInt> for Add {}

impl_operation_for_add_no_addassign!(BigUint);
impl_identity_for_add!(BigUint => BigUint::from_slice(&[]));
impl CommutativeOperation<BigUint> for Add {}

impl<T> Operation<Complex<T>> for Add where Add: Operation<T> {
    fn combine(a: &Complex<T>, b: &Complex<T>) -> Complex<T> {
        Complex {
            re: Add::combine(&a.re, &b.re),
            im: Add::combine(&a.im, &b.im)
        }
    }
    fn combine_mut(a: &mut Complex<T>, b: &Complex<T>) {
        Add::combine_mut(&mut a.re, &b.re);
        Add::combine_mut(&mut a.im, &b.im);
    }
    fn combine_mut2(a: &Complex<T>, b: &mut Complex<T>) {
        Add::combine_mut2(&a.re, &mut b.re);
        Add::combine_mut2(&a.im, &mut b.im);
    }
    fn combine_left(a: Complex<T>, b: &Complex<T>) -> Complex<T> {
        Complex {
            re: Add::combine_left(a.re, &b.re),
            im: Add::combine_left(a.im, &b.im)
        }
    }
    fn combine_right(a: &Complex<T>, b: Complex<T>) -> Complex<T> {
        Complex {
            re: Add::combine_right(&a.re, b.re),
            im: Add::combine_right(&a.im, b.im)
        }
    }
    fn combine_both(a: Complex<T>, b: Complex<T>) -> Complex<T> {
        Complex {
            re: Add::combine_both(a.re, b.re),
            im: Add::combine_both(a.im, b.im)
        }
    }
}
impl<T> CommutativeOperation<Complex<T>> for Add where Add: CommutativeOperation<T> {}
impl<T> Identity<Complex<T>> for Add where Add: Identity<T> {
    fn identity() -> Complex<T> {
        Complex { re: Add::identity(), im: Add::identity() }
    }
}
impl<T> Inverse<Complex<T>> for Add where Add: Inverse<T> {
    fn uncombine(a: &mut Complex<T>, b: &Complex<T>) {
        Add::uncombine(&mut a.re, &b.re);
        Add::uncombine(&mut a.im, &b.im);
    }
}

macro_rules! impl_ratio_op {
    ($op:ty, $add:tt, $sub:tt, $iden:expr) => {
        impl<T: Clone+Integer> Operation<Ratio<T>> for $op {
            fn combine(a: &Ratio<T>, b: &Ratio<T>) -> Ratio<T> {
                a $add b
            }
            fn combine_mut(a: &mut Ratio<T>, b: &Ratio<T>) {
                let aa = mem::replace(a, Add::identity());
                *a = aa $add b;
            }
            fn combine_mut2(a: &Ratio<T>, b: &mut Ratio<T>) {
                let bb = mem::replace(b, Add::identity());
                *b = bb $add a;
            }
            fn combine_left(a: Ratio<T>, b: &Ratio<T>) -> Ratio<T> {
                a $add b
            }
            fn combine_right(a: &Ratio<T>, b: Ratio<T>) -> Ratio<T> {
                b $add a
            }
        }
        impl<T: Clone+Integer> CommutativeOperation<Ratio<T>> for $op {}
        impl<T: Clone+Integer> Identity<Ratio<T>> for $op {
            fn identity() -> Ratio<T> {
                $iden
            }
        }
        impl<T: Clone+Integer> Inverse<Ratio<T>> for $op {
            fn uncombine(a: &mut Ratio<T>, b: &Ratio<T>) {
                let aa = mem::replace(a, Add::identity());
                *a = aa $sub b;
            }
        }
    }
}
impl_ratio_op!(Add, +, -, Ratio::zero());
impl_ratio_op!(Mul, *, /, Ratio::one());

