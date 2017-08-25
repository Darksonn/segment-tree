use std::marker::PhantomData;
use std::mem;

use ops::{Operation, CommutativeOperation, Identity};
use maybe_owned::MaybeOwned;

/// This data structure allows range queries and single element modification.
///
/// This tree allocates `2n * sizeof(N)` bytes of memory.
///
/// This tree is implemented using a segment tree.  A segment tree is a binary tree where each node
/// contains the combination of the children under the operation.
pub struct SegmentPoint<N, O> where O: Operation<N> {
    buf: Vec<N>,
    n: usize,
    op: PhantomData<O>
}

impl<N, O: Operation<N>> SegmentPoint<N, O> {
    /// Builds a tree using the given buffer.  If the given buffer is less than half full, this
    /// function allocates.  This function clones every value in the input array.
    /// Uses `O(len)` time.
    ///
    /// See also the function [`build_noalloc`].
    ///
    /// [`build_noalloc`]: struct.SegmentPoint.html#method.build_noalloc
    pub fn build(mut buf: Vec<N>) -> SegmentPoint<N, O> where N: Clone {
        let n = buf.len();
        buf.reserve_exact(n);
        for i in 0..n {
            debug_assert!(i < buf.len());
            let clone = unsafe { buf.get_unchecked(i).clone() }; // i < n < buf.len()
            buf.push(clone);
        }
        SegmentPoint::build_noalloc(buf)
    }
    /// Computes `a[l] * a[l+1] * ... * a[r-1]`.
    ///
    /// If `l >= r`, this method returns `None`.  This method clones at most twice and runs in
    /// `O(log(len))` time.
    ///
    /// See [`quick_query`] or [`noclone_query`] for a version that doesn't clone.
    ///
    /// [`noclone_query`]: struct.SegmentPoint.html#method.noclone_query
    /// [`quick_query`]: struct.SegmentPoint.html#method.quick_query
    pub fn query(&self, mut l: usize, mut r: usize) -> Option<N> where N: Clone {
        let mut resl = None;
        let mut resr = None;
        l += self.n; r += self.n;
        while l < r {
            if l&1 == 1 {
                resl = match resl {
                    None => Some(self.buf[l].clone()),
                    Some(v) => Some(O::combine_left(v, &self.buf[l]))
                };
                l += 1;
            }
            if r&1 == 1 {
                r -= 1;
                resr = match resr {
                    None => Some(self.buf[r].clone()),
                    Some(v) => Some(O::combine_right(&self.buf[r], v))
                }
            }
            l >>= 1; r >>= 1;
        }
        match resl {
            None => resr,
            Some(l) => match resr {
                None => Some(l),
                Some(r) => Some(O::combine_both(l, r))
            }
        }
    }
    /// Computes `a[l] * a[l+1] * ... * a[r-1]`.
    ///
    /// If `l >= r`, this method returns `None`.
    /// Uses `O(log(len))` time.
    ///
    /// See also [`query`] and [`quick_query`].
    ///
    /// [`quick_query`]: struct.SegmentPoint.html#method.quick_query
    /// [`query`]: struct.SegmentPoint.html#method.query
    pub fn noclone_query<'a>(&'a self, mut l: usize, mut r: usize) -> Option<MaybeOwned<'a, N>> {
        let mut resl = None;
        let mut resr = None;
        l += self.n; r += self.n;
        while l < r {
            if l&1 == 1 {
                resl = match resl {
                    None => Some(MaybeOwned::Borrowed(&self.buf[l])),
                    Some(MaybeOwned::Borrowed(ref v)) => Some(MaybeOwned::Owned(O::combine(v, &self.buf[l]))),
                    Some(MaybeOwned::Owned(v)) => Some(MaybeOwned::Owned(O::combine_left(v, &self.buf[l]))),
                };
                l += 1;
            }
            if r&1 == 1 {
                r -= 1;
                resr = match resr {
                    None => Some(MaybeOwned::Borrowed(&self.buf[r])),
                    Some(MaybeOwned::Borrowed(ref v)) => Some(MaybeOwned::Owned(O::combine(&self.buf[r], v))),
                    Some(MaybeOwned::Owned(v)) => Some(MaybeOwned::Owned(O::combine_right(&self.buf[r], v))),
                }
            }
            l >>= 1; r >>= 1;
        }
        match resl {
            None => resr,
            Some(MaybeOwned::Borrowed(ref l)) => match resr {
                None => Some(MaybeOwned::Borrowed(l)),
                Some(MaybeOwned::Borrowed(ref r)) => Some(MaybeOwned::Owned(O::combine(l, r))),
                Some(MaybeOwned::Owned(r)) => Some(MaybeOwned::Owned(O::combine_right(l, r)))
            },
            Some(MaybeOwned::Owned(l)) => match resr {
                None => Some(MaybeOwned::Owned(l)),
                Some(MaybeOwned::Borrowed(ref r)) => Some(MaybeOwned::Owned(O::combine_left(l, r))),
                Some(MaybeOwned::Owned(r)) => Some(MaybeOwned::Owned(O::combine_both(l, r)))
            }
        }
    }
    /// Set the value at the specified index and return the old value.
    /// Uses `O(log(len))` time.
    pub fn modify(&mut self, mut p: usize, value: N) -> N {
        p += self.n;
        let res = mem::replace(&mut self.buf[p], value);
        while { p >>= 1; p > 0 } {
            self.buf[p] = O::combine(&self.buf[p<<1], &self.buf[p<<1|1]);
        }
        res
    }
    /// Combine the value at `p` with `delta`, such that `delta` is the left argument.
    /// Uses `O(log(len))` time.
    pub fn compose_left(&mut self, mut p: usize, delta: &N) {
        p += self.n;
        O::combine_mut2(delta, &mut self.buf[p]);
        while { p >>= 1; p > 0 } {
            self.buf[p] = O::combine(&self.buf[p<<1], &self.buf[p<<1|1]);
        }
    }
    /// Combine the value at `p` with `delta`, such that `delta` is the right argument.
    /// Uses `O(log(len))` time.
    pub fn compose_right(&mut self, mut p: usize, delta: &N) {
        p += self.n;
        O::combine_mut(&mut self.buf[p], delta);
        while { p >>= 1; p > 0 } {
            self.buf[p] = O::combine(&self.buf[p<<1], &self.buf[p<<1|1]);
        }
    }
    /// View the values in this segment tree using a slice.  Uses `O(1)` time.
    #[inline(always)]
    pub fn view(&self) -> &[N] {
        &self.buf[self.n..]
    }
    /// The number of elements stored in this segment tree.  Uses `O(1)` time.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.n
    }
    /// Builds a tree using the given buffer.  The buffer must be even in size.
    /// The first `n` values have no effect on the resulting tree,
    /// and the remaining `n` values contains the array to build the tree on.
    /// Uses `O(len)` time.
    ///
    /// This function panics if the size of the buffer is odd.
    pub fn build_noalloc(mut buf: Vec<N>) -> SegmentPoint<N, O> {
        let len = buf.len();
        let n = len >> 1;
        if len & 1 == 1 {
            panic!("SegmentPoint::build_noalloc: odd size");
        }
        for i in (1..n).rev() {
            let res = O::combine(&buf[i<<1], &buf[i<<1 | 1]);
            buf[i] = res;
        }
        SegmentPoint {
            buf: buf, op: PhantomData, n: n
        }
    }
}
impl<N, O: CommutativeOperation<N>> SegmentPoint<N, O> {
    /// Combine the value at `p` with `delta`.
    /// Uses `O(log(len))` time.
    #[inline(always)]
    pub fn compose(&mut self, p: usize, delta: &N) {
        self.compose_right(p, delta);
    }
}
impl<N, O: CommutativeOperation<N> + Identity<N>> SegmentPoint<N, O> {
    /// Computes `a[l] * a[l+1] * ... * a[r-1]`.
    /// Uses `O(log(len))` time.
    ///
    /// If `l >= r`, this method returns the identity.
    ///
    /// See [`query`] or [`noclone_query`] for a version that works with non-[commutative operations][1].
    ///
    /// [`query`]: struct.SegmentPoint.html#method.query
    /// [`noclone_query`]: struct.SegmentPoint.html#method.noclone_query
    /// [1]: ops/trait.CommutativeOperation.html
    pub fn quick_query(&self, mut l: usize, mut r: usize) -> N {
        let mut res = O::identity();
        l += self.n; r += self.n;
        while l < r {
            if l&1 == 1 {
                res = O::combine_left(res, &self.buf[l]);
                l += 1;
            }
            if r&1 == 1 {
                r -= 1;
                res = O::combine_left(res, &self.buf[r]);
            }
            l >>= 1; r >>= 1;
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use SegmentPoint;
    use ops::*;
    use maybe_owned::MaybeOwned;
    use rand::{Rand, Rng, thread_rng};
    use std::num::Wrapping;

    /// Not commutative! Not useful in practice since the root always contains the concatenation of
    /// every string.
    #[derive(PartialEq, Eq, Clone, Debug)]
    struct StrType {
        value: String
    }
    impl StrType {
        fn cat(list: &[StrType]) -> StrType {
            let mut res = String::new();
            for v in list {
                res.push_str(v.value.as_str());
            }
            StrType { value: res }
        }
        fn sub(&self, i: usize, j: usize) -> StrType {
            StrType { value: String::from(&self.value[4*i .. 4*j]) }
        }
    }
    impl Rand for StrType {
        fn rand<R: Rng>(rng: &mut R) -> Self {
            StrType { value: rng.gen_ascii_chars().take(4).collect() }
        }
    }
    impl Operation<StrType> for Add {
        fn combine(a: &StrType, b: &StrType) -> StrType {
            StrType {
                value: a.value.clone() + b.value.as_str()
            }
        }
        fn combine_mut(a: &mut StrType, b: &StrType) {
            a.value.push_str(b.value.as_str());
        }
    }

    #[test]
    fn segment_tree_build() {
        let mut rng = thread_rng();
        let vals: Vec<_> = rng.gen_iter::<i32>().map(|i| Wrapping(i)).take(130).collect();
        for i in 0..vals.len() {
            let buf: Vec<_> = vals[0..i].iter().cloned().collect();
            println!("{:?}", buf);
            let mut buf2 = vec![];
            let n = buf.len();
            buf2.resize(2*n, Wrapping(0));
            for i in 0..n {
                buf2[n+i] = buf[i];
            }
            let tree1: SegmentPoint<Wrapping<i32>, Add>
                = SegmentPoint::build(buf);
            let tree2: SegmentPoint<Wrapping<i32>, Add>
                = SegmentPoint::build_noalloc(buf2);
            let mut buf = tree1.buf;
            let mut buf2 = tree2.buf;
            if i > 0 {
                buf[0] = Wrapping(0);
                buf2[0] = Wrapping(0);
            }
            println!("build");
            println!("{:?}", buf);
            println!("build_noalloc");
            println!("{:?}", buf2);
            assert_eq!(buf, buf2);
            assert_eq!(buf.len(), 2*n);
        }
    }
    #[test]
    fn segment_tree_query() {
        let mut rng = thread_rng();
        let vals: Vec<StrType> = rng.gen_iter().take(130).collect();
        for i in 0..vals.len() {
            let buf: Vec<_> = vals[0..i].iter().cloned().collect();
            let tree: SegmentPoint<_, Add> = SegmentPoint::build(buf.clone());
            let sum = StrType::cat(&buf);
            let n = buf.len();
            println!("n: {} tree.buf.len: {}", n, tree.buf.len());
            for i in 0..n {
                assert_eq!(tree.query(i, i), None);
                for j in i+1..n+1 {
                    println!("i: {}, j: {}", i, j);
                    assert_eq!(tree.query(i, j), Some(sum.sub(i, j)));
                    assert_eq!(tree.noclone_query(i, j), Some(MaybeOwned::Owned(sum.sub(i, j))));
                }
            }
        }
    }
    #[test]
    fn segment_tree_quick_query() {
        let mut rng = thread_rng();
        let vals: Vec<Wrapping<i32>> = rng.gen_iter().map(|i| Wrapping(i)).take(130).collect();
        for i in 0..vals.len() {
            let mut buf: Vec<_> = vals[0..i].iter().cloned().collect();
            let tree: SegmentPoint<_, Add> = SegmentPoint::build(buf.clone());
            assert_eq!(tree.view(), &buf[..]);
            for i in 1..buf.len() { buf[i] += buf[i-1]; } // compute the prefix sum
            let n = buf.len();
            println!("n: {} tree.buf.len: {}", n, tree.buf.len());
            for i in 0..n {
                assert_eq!(tree.query(i, i), None);
                for j in i+1..n+1 {
                    println!("i: {}, j: {}", i, j);
                    if i == 0 {
                        assert_eq!(tree.quick_query(i, j), buf[j-1]);
                    } else {
                        assert_eq!(tree.quick_query(i, j), buf[j-1] - buf[i-1]);
                    }
                }
            }
        }
    }
    #[test]
    fn segment_tree_modify() {
        let mut rng = thread_rng();
        let vals1: Vec<Wrapping<i32>> = rng.gen_iter::<i32>().map(|i| Wrapping(i)).take(130).collect();
        let vals2: Vec<Wrapping<i32>> = rng.gen_iter::<i32>().map(|i| Wrapping(i)).take(130).collect();
        for i in 0..vals1.len() {
            let mut order: Vec<_> = (0..i).collect();
            rng.shuffle(&mut order[..]);
            let mut buf: Vec<_> = vals1[0..i].iter().cloned().collect();
            let mut tree: SegmentPoint<Wrapping<i32>, Add> = SegmentPoint::build(buf.clone());
            for next in order {
                tree.modify(next, vals2[next]);
                buf[next] = vals2[next];
                let tree2: SegmentPoint<Wrapping<i32>, Add> = SegmentPoint::build(buf.clone());
                assert_eq!(tree.buf[1..], tree2.buf[1..]);
            }
        }
    }
}
