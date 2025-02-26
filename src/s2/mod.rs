mod stuv;

pub mod cell;
pub mod cellid;
pub mod cellunion;

pub mod cap;
pub mod latlng;
pub mod point;
// pub mod polygon;
pub mod rect;
pub mod rect_bounder;

pub mod region;

pub mod edgeutil;
pub mod metric;
pub mod predicates;

pub mod shape;

mod edge_crosser;
mod edge_crossings;
// mod loops;
#[cfg(test)]
mod random;
mod edge_clipping;
