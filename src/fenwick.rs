use std::ops::{Add, Sub, Mul};

/// This data structure allows prefix queries and single element modification.
///
/// This tree allocates `n * sizeof(N)` bytes of memory, and can be resized.
///
/// This data structure is implemented using a fenwick tree, which is also known as a binary
/// indexed tree.
#[derive(Clone)]
pub struct PrefixPoint<N> {
    buf: Vec<N>
}

/// Returns the least significant bit which is one.
#[inline(always)]
fn lsb(i: usize) -> usize {
    i & (1 + !i)
}

impl<N> PrefixPoint<N> {
    /// Returns the number of values in this tree.
    pub fn len(&self) -> usize {
        self.buf.len()
    }
}
impl<N: Add<Output=N> + Copy> PrefixPoint<N> {
    /// Creates a `PrefixPoint` containing the given values.  Uses `O(len)` time.
    pub fn build(mut buf: Vec<N>) -> PrefixPoint<N> {
        let len = buf.len();
        for i in 0..len {
            let j = i + lsb(i+1);
            if j < len {
                buf[j] = buf[i] + buf[j];
            }
        }
        PrefixPoint { buf: buf }
    }
    #[inline]
    /// Computes the sum of the values from 0 to `i`, including `i`.  Uses `O(log(i))` time.
    pub fn sum(&self, mut i: usize) -> N {
        let mut sum = self.buf[i];
        i -= lsb(1+i) - 1;
        while i > 0 {
            sum = self.buf[i-1] + sum;
            i -= lsb(i);
        }
        sum
    }
    #[inline]
    /// Adds `delta` to the value at `i`.  Uses `O(log(len))` time.
    pub fn add(&mut self, mut i: usize, delta: N) {
        let len = self.buf.len();
        while i < len {
            self.buf[i] = self.buf[i] + delta;
            i += lsb(i+1);
        }
    }
    #[inline(always)]
    /// Truncates the `PrefixPoint` to the given size.  If `size >= len`, this method does nothing.
    /// Uses `O(1)` time.
    pub fn truncate(&mut self, size: usize) {
        self.buf.truncate(size);
    }
    /// Adds the given values to the `PrefixPoint`, increasing its size.  Uses `O(len)` time.
    #[inline]
    pub fn append(&mut self, mut values: Vec<N>) {
        self.extend(values.drain(..))
    }
}
impl<N: Add<Output=N> + Copy> Extend<N> for PrefixPoint<N> {
    /// Adds the given values to the `PrefixPoint`, increasing its size.  Uses `O(len)` time.
    fn extend<I: IntoIterator<Item=N>>(&mut self, values: I) {
        let oldlen = self.buf.len();
        self.buf.extend(values);
        let len = self.buf.len();
        for i in 0..len {
            let j = i + lsb(i+1);
            if oldlen <= j && j < len {
                self.buf[j] = self.buf[i] + self.buf[j];
            }
        }
    }
}
impl<N: Add<Output=N> + Sub<Output=N> + Copy> PrefixPoint<N> {
    /// Returns the value at `i`.
    /// Uses `O(log(i))` time.
    /// Store your own copy of the array if you want constant time.
    /// Assumes that `a + b = b + a` and that `a + b - b = a`.
    pub fn get(&self, mut i: usize) -> N {
        let mut sum = self.buf[i];
        let z = 1 + i - lsb(i+1);
        while i != z {
            sum = sum - self.buf[i-1];
            i -= lsb(i);
        }
        sum
    }
    /// Compute the underlying array of values.
    /// Uses `O(len)` time.
    /// Assumes that `a + b = b + a` and that `a + b - b = a`.
    pub fn unwrap(self) -> Vec<N> {
        let mut buf = self.buf;
        let len = buf.len();
        for i in (0..len).rev() {
            let j = i + lsb(i+1);
            if j < len {
                buf[j] = buf[j] - buf[i];
            }
        }
        buf
    }
}
impl<N: Mul<Output=N> + Copy> PrefixPoint<N> {
    #[inline]
    /// Multiplies every value in the PrefixPoint with `scale`.  Uses `O(len)` time.
    pub fn scale(&mut self, scale: N) {
        for val in &mut self.buf {
            *val = *val * scale;
        }
    }
}

#[cfg(test)]
mod tests {

    /// Modifies the given slice such that the n'th element becomes the sum of the first n elements.
    pub fn compute_prefix_sum<N: Add<Output=N> + Copy>(buf: &mut[N]) {
        let mut iter = buf.iter_mut();
        match iter.next() {
            None => {},
            Some(s) => {
                let mut sum = *s;
                for item in iter {
                    sum = sum + *item;
                    *item = sum;
                }
            }
        }
    }

    use super::*;
    use rand::{Rng, thread_rng};
    use std::num::Wrapping;

    #[test]
    fn fenwick() {
        let mut rng = thread_rng();
        for n in 0..130 {
            let mut vec: Vec<Wrapping<i32>> = rng.gen_iter::<i32>().take(n).map(|i| Wrapping(i)).collect();
            let fenwick = PrefixPoint::build(vec.clone());
            compute_prefix_sum(&mut vec);
            for i in 0..vec.len() {
                assert_eq!(vec[i], fenwick.sum(i));
            }
        }
    }
    #[test]
    fn fenwick_scale() {
        let mut rng = thread_rng();
        for n in 0..130 {
            let mut vec: Vec<Wrapping<i32>> = rng.gen_iter::<i32>().take(n).map(|i| Wrapping(i)).collect();
            let mut fenwick = PrefixPoint::build(vec.clone());
            assert_eq!(fenwick.clone().unwrap(), vec);
            compute_prefix_sum(&mut vec);
            fenwick.scale(Wrapping(12));
            for i in 0..vec.len() {
                assert_eq!(vec[i]*Wrapping(12), fenwick.sum(i));
            }
        }
    }
    #[test]
    fn fenwick_add_get() {
        let mut rng = thread_rng();
        for n in 0..130 {
            let mut vec: Vec<Wrapping<i32>> = rng.gen_iter::<i32>().take(n).map(|i| Wrapping(i)).collect();
            let diff: Vec<Wrapping<i32>> = rng.gen_iter::<i32>().take(n).map(|i| Wrapping(i)).collect();
            let mut fenwick = PrefixPoint::build(vec.clone());
            for i in 0..diff.len() {
                let mut ps: Vec<Wrapping<i32>> = vec.clone();
                compute_prefix_sum(&mut ps);
                assert_eq!(fenwick.clone().unwrap(), vec);
                for j in 0..vec.len() {
                    assert_eq!(ps[j], fenwick.sum(j));
                    assert_eq!(vec[j], fenwick.get(j));
                }
                vec[i] += diff[i];
                fenwick.add(i, diff[i]);
            }
        }
    }
    #[test]
    fn fenwick_extend() {
        let mut rng = thread_rng();
        for n in 0..130 {
            let vec: Vec<Wrapping<i32>> = rng.gen_iter::<i32>().take(n).map(|i| Wrapping(i)).collect();
            let mut sum = vec.clone();
            compute_prefix_sum(&mut sum);
            for i in 0..sum.len() {
                let mut fenwick = PrefixPoint::build(vec.iter().take(i/2).map(|&i| i).collect());
                fenwick.extend(vec.iter().skip(i/2).take(i - i/2).map(|&i| i));
                for j in 0..i {
                    assert_eq!(sum[j], fenwick.sum(j));
                }
            }
        }
    }
}
