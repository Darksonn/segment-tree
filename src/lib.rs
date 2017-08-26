//! This crate contains various data structures useful for quickly performing interval queries or
//! modifications in some array.
//!
//! The data structures in this crate are all trees. The trees are represented using an array for
//! high performance and low memory usage.
//! Despite the name of the crate, not every tree in this crate is a segment tree.
//!
//! The [`SegmentPoint`] data structure allows solving the [range minimum query][1] problem, as
//! well as performing any operator (such as addition or matrix multiplication) over any interval.
//! This is the data structure traditionally known as a segment tree.
//!
//! The [`PointSegment`] data structure allows doing something to every value in some interval
//! using only logaritmic time. For example add `5` to every value with indices between `5000` and
//! `30000`.
//!
//! The [`PrefixPoint`] data structure is a weaker version of the [`SegmentPoint`] data structure,
//! since the intervals must start at the index `0` and the operator must be [commutative][2].
//! However it has the advantage that it uses half the memory and the size of the array can be
//! changed.
//!
//! This crate has an optional feature `num-ops` that add implementations of the types from the
//! `num` crate to [`ops`].
//!
//! [1]: https://en.wikipedia.org/wiki/Range_minimum_query
//! [2]: ops/trait.CommutativeOperation.html
//! [`SegmentPoint`]: struct.SegmentPoint.html
//! [`PointSegment`]: struct.PointSegment.html
//! [`PrefixPoint`]: struct.PrefixPoint.html
//! [`ops`]: ops/index.html

pub mod ops;
pub mod maybe_owned;
pub use fenwick::PrefixPoint;
pub use propogating::PointSegment;
pub use range_query::SegmentPoint;

mod fenwick;
mod propogating;
mod range_query;

#[cfg(test)]
extern crate rand;

#[cfg(feature = "num-ops")]
extern crate num;
