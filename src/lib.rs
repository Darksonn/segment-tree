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
