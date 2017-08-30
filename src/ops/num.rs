//! This module requires the `with-num` feature and supplies implementations for various types from
//! the `num` crate.

use ops::{Operation, CommutativeOperation, Identity, Inverse};
use ops::{Add, Mul};
use num::{BigInt, BigUint, Complex, Zero, One};
use num::bigint::Sign;
use num::integer::Integer;
use num::rational::Ratio;

use std::mem;

macro_rules! impl_big {
    ($t:ty) => {
        impl Operation<$t> for Add {
            fn combine(&self, a: &$t, b: &$t) -> $t {
                a.clone() + b
            }
            fn combine_mut(&self, a: &mut $t, b: &$t) {
                let aa = mem::replace(a, self.identity());
                *a = aa + b;
            }
            fn combine_mut2(&self, a: &$t, b: &mut $t) {
                let bb = mem::replace(b, self.identity());
                *b = bb + a;
            }
            fn combine_left(&self, a: $t, b: &$t) -> $t {
                a + b
            }
            fn combine_right(&self, a: &$t, b: $t) -> $t {
                b + a
            }
        }
        impl Operation<$t> for Mul {
            fn combine(&self, a: &$t, b: &$t) -> $t {
                a.clone() * b
            }
            fn combine_mut(&self, a: &mut $t, b: &$t) {
                let aa = mem::replace(a, self.identity());
                *a = aa * b;
            }
            fn combine_mut2(&self, a: &$t, b: &mut $t) {
                let bb = mem::replace(b, self.identity());
                *b = bb * a;
            }
            fn combine_left(&self, a: $t, b: &$t) -> $t {
                a * b
            }
            fn combine_right(&self, a: &$t, b: $t) -> $t {
                b * a
            }
        }
        impl Inverse<$t> for Add {
            fn uncombine(&self, a: &mut $t, b: &$t) {
                let aa = mem::replace(a, self.identity());
                *a = aa - b;
            }
        }
        impl Inverse<$t> for Mul {
            fn uncombine(&self, a: &mut $t, b: &$t) {
                let aa = mem::replace(a, self.identity());
                *a = aa / b;
            }
        }
    }
}

macro_rules! impl_iden_add {
    ($t:ty => $iden:expr) => {
        impl Identity<$t> for Add {
            fn identity(&self) -> $t {
                $iden
            }
        }
    }
}
macro_rules! impl_iden_mul {
    ($t:ty => $iden:expr) => {
        impl Identity<$t> for Mul {
            fn identity(&self) -> $t {
                $iden
            }
        }
    }
}

impl_big!(BigInt);
impl_iden_add!(BigInt => BigInt::from_slice(Sign::NoSign, &[]));
impl_iden_mul!(BigInt => BigInt::from_slice(Sign::Plus, &[1]));
impl CommutativeOperation<BigInt> for Add {}

impl_big!(BigUint);
impl_iden_add!(BigUint => BigUint::from_slice(&[]));
impl_iden_mul!(BigUint => BigUint::from_slice(&[1]));
impl CommutativeOperation<BigUint> for Add {}

impl<T> Operation<Complex<T>> for Add where Add: Operation<T> {
    fn combine(&self, a: &Complex<T>, b: &Complex<T>) -> Complex<T> {
        Complex {
            re: self.combine(&a.re, &b.re),
            im: self.combine(&a.im, &b.im)
        }
    }
    fn combine_mut(&self, a: &mut Complex<T>, b: &Complex<T>) {
        self.combine_mut(&mut a.re, &b.re);
        self.combine_mut(&mut a.im, &b.im);
    }
    fn combine_mut2(&self, a: &Complex<T>, b: &mut Complex<T>) {
        self.combine_mut2(&a.re, &mut b.re);
        self.combine_mut2(&a.im, &mut b.im);
    }
    fn combine_left(&self, a: Complex<T>, b: &Complex<T>) -> Complex<T> {
        Complex {
            re: self.combine_left(a.re, &b.re),
            im: self.combine_left(a.im, &b.im)
        }
    }
    fn combine_right(&self, a: &Complex<T>, b: Complex<T>) -> Complex<T> {
        Complex {
            re: self.combine_right(&a.re, b.re),
            im: self.combine_right(&a.im, b.im)
        }
    }
    fn combine_both(&self, a: Complex<T>, b: Complex<T>) -> Complex<T> {
        Complex {
            re: self.combine_both(a.re, b.re),
            im: self.combine_both(a.im, b.im)
        }
    }
}
impl<T> CommutativeOperation<Complex<T>> for Add where Add: CommutativeOperation<T> {}
impl<T> Identity<Complex<T>> for Add where Add: Identity<T> {
    fn identity(&self) -> Complex<T> {
        Complex { re: self.identity(), im: self.identity() }
    }
}
impl<T> Inverse<Complex<T>> for Add where Add: Inverse<T> {
    fn uncombine(&self, a: &mut Complex<T>, b: &Complex<T>) {
        self.uncombine(&mut a.re, &b.re);
        self.uncombine(&mut a.im, &b.im);
    }
}

macro_rules! impl_ratio_op {
    ($op:ty, $add:tt, $sub:tt, $iden:expr) => {
        impl<T: Clone+Integer> Operation<Ratio<T>> for $op {
            fn combine(&self, a: &Ratio<T>, b: &Ratio<T>) -> Ratio<T> {
                a $add b
            }
            fn combine_mut(&self, a: &mut Ratio<T>, b: &Ratio<T>) {
                let aa = mem::replace(a, self.identity());
                *a = aa $add b;
            }
            fn combine_mut2(&self, a: &Ratio<T>, b: &mut Ratio<T>) {
                let bb = mem::replace(b, self.identity());
                *b = bb $add a;
            }
            fn combine_left(&self, a: Ratio<T>, b: &Ratio<T>) -> Ratio<T> {
                a $add b
            }
            fn combine_right(&self, a: &Ratio<T>, b: Ratio<T>) -> Ratio<T> {
                b $add a
            }
        }
        impl<T: Clone+Integer> CommutativeOperation<Ratio<T>> for $op {}
        impl<T: Clone+Integer> Identity<Ratio<T>> for $op {
            fn identity(&self) -> Ratio<T> {
                $iden
            }
        }
        impl<T: Clone+Integer> Inverse<Ratio<T>> for $op {
            fn uncombine(&self, a: &mut Ratio<T>, b: &Ratio<T>) {
                let aa = mem::replace(a, self.identity());
                *a = aa $sub b;
            }
        }
    }
}
impl_ratio_op!(Add, +, -, Ratio::zero());
impl_ratio_op!(Mul, *, /, Ratio::one());

