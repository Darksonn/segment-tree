use std::marker::PhantomData;
use std::mem;
use std::iter::repeat;

use ops::{CommutativeOperation, Identity};

/// This data structure allows range modification and single element queries.
///
/// This tree allocates `2n * sizeof(N)` bytes of memory.
///
/// This tree is implemented using a binary tree, where each node contains the changes that need
/// to be propogated to its children.
pub struct PointSegment<N, O> where O: CommutativeOperation<N> + Identity<N> {
    buf: Vec<N>,
    n: usize,
    op: PhantomData<O>
}

impl<N, O: CommutativeOperation<N> + Identity<N>> PointSegment<N, O> {
    /// Builds a tree using the given buffer. If the given buffer is less than half full, this
    /// function allocates.
    /// Uses `O(len)` time.
    pub fn build(mut buf: Vec<N>) -> PointSegment<N, O> {
        let n = buf.len();
        buf.reserve_exact(n);
        for i in 0..n {
            let val = mem::replace(&mut buf[i], O::identity());
            buf.push(val);
        }
        PointSegment { buf: buf, n: n, op: PhantomData }
    }
    /// Allocate a new buffer and build the tree using the values in the slice.
    /// Uses `O(len)` time.
    pub fn build_slice(buf: &[N]) -> PointSegment<N, O> where N: Clone {
        let n = buf.len();
        PointSegment {
            buf: repeat(O::identity()).take(n).chain(buf.iter().cloned()).collect(),
            n: n, op: PhantomData
        }
    }
    /// Allocate a new buffer and build the tree using the values in the iterator.
    /// Uses `O(len)` time.
    pub fn build_iter<I: ExactSizeIterator<Item=N>>(iter: I) -> PointSegment<N, O> {
        let n = iter.len();
        let mut buf = Vec::with_capacity(2*n);
        for _ in 0..n { buf.push(O::identity()); }
        buf.extend(iter);
        PointSegment {
            buf: buf,
            n: n, op: PhantomData
        }
    }
    /// Computes the value at `p`.
    /// Uses `O(log(len))` time.
    pub fn query(&self, mut p: usize) -> N {
        p += self.n;
        let mut res = O::identity();
        while p > 0 {
            res = O::combine_left(res, &self.buf[p]);
            p >>= 1;
        }
        res
    }
    /// Combine every value in the interval with `delta`.
    /// Uses `O(log(len))` time.
    pub fn modify(&mut self, mut l: usize, mut r: usize, delta: N) {
        l += self.n; r += self.n;
        while l < r {
            if l&1 == 1 {
                O::combine_mut(&mut self.buf[l], &delta);
                l += 1;
            }
            if r&1 == 1 {
                r -= 1;
                O::combine_mut(&mut self.buf[r], &delta);
            }
            l >>= 1; r >>= 1;
        }
    }
    /// Propogate all changes to the leaves in the tree and return a mutable slice containing the
    /// leaves.
    /// Uses `O(len)` time.
    pub fn propogate(&mut self) -> &mut [N] {
        for i in 1..self.n {
            let prev = mem::replace(&mut self.buf[i], O::identity());
            O::combine_mut(&mut self.buf[i<<1], &prev);
            O::combine_mut(&mut self.buf[i<<1|1], &prev);
        }
        &mut self.buf[self.n..]
    }
    /// Returns the number of values in the underlying array.
    /// Uses `O(1)` time.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.n
    }
}

#[cfg(test)]
mod tests {
    use propogating::*;
    use ops::*;
    use rand::{Rng, thread_rng};
    use std::num::Wrapping;

    type Num = Wrapping<i32>;

    #[test]
    fn test() {
        let mut rng = thread_rng();
        for i in 1..130 {
            let mut buf: Vec<Num> = rng.gen_iter::<i32>().map(|i| Wrapping(i)).take(i).collect();
            let mut tree: PointSegment<_,Add> = if i&1 == 1 {
                PointSegment::build_slice(&buf[..])
            } else {
                PointSegment::build(buf.clone())
            };
            for (n, m, v) in rng.gen_iter::<(usize, usize, i32)>().take(10) {
                let n = n % i;
                let m = m % i;
                if n > m { continue; }
                for index in n..m { buf[index] += Wrapping(v); }
                tree.modify(n, m, Wrapping(v));
                for index in 0..i {
                    assert_eq!(buf[index], tree.query(index));
                }
            }
            assert_eq!(&mut buf[..], tree.propogate());
        }
    }
}
