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

// TODO: Disable to allow testing of other modules
pub mod loops;

mod edge_crosser;
mod edge_crossings;
#[cfg(test)]
mod random;
mod edge_clipping;
pub mod shape_index;
pub mod shape_index_region;
pub mod lax_loop;
pub mod polygon;
pub mod crossing_edge_query;
pub mod padded_cell;
pub mod error;
