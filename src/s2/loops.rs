// Copyright 2015 Google Inc. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::cmp::Ordering;
use std::f64::consts::PI;

use crate::cell::Cell;
use crate::point::Point;
use crate::r1;
use crate::r3::vector::Vector;
use crate::rect::Rect;
use crate::s1;
use crate::s2::edge_crossings::angle_contains_vertex;
use crate::s2::edge_crossings::{EdgeCrosser, ChainEdgeCrosser};
use crate::s2::predicates::*;
use crate::s2::error::{S2Error, S2Result};
use crate::consts::EPSILON;

/// Loop represents a simple spherical polygon. It consists of a sequence
/// of vertices where the first vertex is implicitly connected to the
/// last. All loops are defined to have a CCW orientation, i.e. the interior of
/// the loop is on the left side of the edges. This implies that a clockwise
/// loop enclosing a small area is interpreted to be a CCW loop enclosing a
/// very large area.
///
/// Loops are not allowed to have any duplicate vertices (whether adjacent or
/// not). Non-adjacent edges are not allowed to intersect, and furthermore edges
/// of length 180 degrees are not allowed (i.e., adjacent vertices cannot be
/// antipodal). Loops must have at least 3 vertices (except for the "empty" and
/// "full" loops discussed below).
///
/// There are two special loops: the "empty" loop contains no points and the
/// "full" loop contains all points. These loops do not have any edges, but to
/// preserve the invariant that every loop can be represented as a vertex
/// chain, they are defined as having exactly one vertex each (see empty_loop
/// and full_loop).
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Loop {
    /// The vertices of the loop
    vertices: Vec<Point>,

    /// origin_inside keeps a precomputed value whether this loop contains the origin
    /// versus computing from the set of vertices every time.
    origin_inside: bool,

    /// depth is the nesting depth of this Loop if it is contained by a Polygon
    /// or other shape and is used to determine if this loop represents a hole
    /// or a filled in portion.
    depth: i64,

    /// bound is a conservative bound on all points contained by this loop.
    /// If self.contains_point(P), then self.bound.contains_point(P).
    bound: Rect,

    /// Since bound is not exact, it is possible that a loop A contains
    /// another loop B whose bounds are slightly larger. subregion_bound
    /// has been expanded sufficiently to account for this error, i.e.
    /// if A.contains(B), then A.subregion_bound.contains(B.bound).
    subregion_bound: Rect,

    /// index is the spatial index for this Loop.
    index: Option<ShapeIndex>,
}

// These two points are used for the special Empty and Full loops.
lazy_static::lazy_static! {
    static ref EMPTY_LOOP_POINT: Point = Point(Vector { x: 0.0, y: 0.0, z: 1.0 });
    static ref FULL_LOOP_POINT: Point = Point(Vector { x: 0.0, y: 0.0, z: -1.0 });
}

impl Loop {
    /// init_origin_and_bound sets the origin containment for the given point and then calls
    /// the initialization for the bounds objects and the internal index.
    fn init_origin_and_bound(&mut self) {
        if self.vertices.len() < 3 {
            // Check for the special "empty" and "full" loops (which have one vertex).
            if !self.is_empty_or_full() {
                self.origin_inside = false;
                return;
            }
            // This is the special empty or full loop, so the origin depends on if
            // the vertex is in the southern hemisphere or not.
            self.origin_inside = self.vertices[0].0.z < 0.0;
        } else {
            // The brute force point containment algorithm works by counting edge
            // crossings starting at a fixed reference point (chosen as origin_point()
            // for historical reasons). Loop initialization would be more efficient
            // if we used a loop vertex such as vertex(0) as the reference point
            // instead, however making this change would be a lot of work because
            // origin_inside is currently part of the Encode() format.
            //
            // In any case, we initialize origin_inside by first guessing that it is
            // outside, and then seeing whether we get the correct containment result
            // for vertex 1. If the result is incorrect, the origin must be inside
            // the loop instead. Note that the Loop is not necessarily valid and so
            // we need to check the requirements of angle_contains_vertex first.
            let v1_inside = self.vertices[0] != self.vertices[1] &&
                self.vertices[2] != self.vertices[1] &&
                angle_contains_vertex(&self.vertices[0], &self.vertices[1], &self.vertices[2]);

            // initialize before calling contains_point
            self.origin_inside = false;

            // Note that contains_point only does a bounds check once init_index
            // has been called, so it doesn't matter that bound is undefined here.
            if v1_inside != self.contains_point(self.vertices[1]) {
                self.origin_inside = true;
            }
        }

        // We *must* call init_bound before initializing the index, because
        // init_bound calls contains_point which does a bounds check before using
        // the index.
        self.init_bound();

        // Create a new index and add us to it.
        self.index = Some(ShapeIndex::new());
        // TODO: Add self to the index
        // if let Some(index) = &mut self.index {
        //     index.add(self);
        // }
    }

    /// from_points constructs a loop from the given points.
    pub fn from_points(pts: &[Point]) -> Self {
        let mut l = Loop::default();
        l.vertices = pts.to_vec();

        l.init_origin_and_bound();
        l
    }

    /// from_cell constructs a loop corresponding to the given cell.
    ///
    /// Note that the loop and cell *do not* contain exactly the same set of
    /// points, because Loop and Cell have slightly different definitions of
    /// point containment. For example, a Cell vertex is contained by all
    /// four neighboring Cells, but it is contained by exactly one of four
    /// Loops constructed from those cells. As another example, the cell
    /// coverings of cell and from_cell(cell) will be different, because the
    /// loop contains points on its boundary that actually belong to other cells
    /// (i.e., the covering will include a layer of neighboring cells).
    pub fn from_cell(c: &Cell) -> Self {
        Self::from_points(&c.vertices())
    }

    /// empty_loop returns a special "empty" loop.
    pub fn empty_loop() -> Self {
        Self::from_points(&[EMPTY_LOOP_POINT.clone()])
    }

    /// full_loop returns a special "full" loop.
    pub fn full_loop() -> Self {
        Self::from_points(&[FULL_LOOP_POINT.clone()])
    }




    /// init_bound sets up the approximate bounding Rects for this loop.
    fn init_bound(&mut self) {
        if self.vertices.is_empty() {
            *self = Self::empty_loop();
            return;
        }
        
        // Check for the special "empty" and "full" loops.
        if self.is_empty_or_full() { 
            if self.is_empty() {
                self.bound = Rect::empty();
            } else {
                self.bound = Rect::full();
            }
            self.subregion_bound = self.bound.clone();
            return;
        }

        // The bounding rectangle of a loop is not necessarily the same as the
        // bounding rectangle of its vertices. First, the maximal latitude may be
        // attained along the interior of an edge. Second, the loop may wrap
        // entirely around the sphere (e.g. a loop that defines two revolutions of a
        // candy-cane stripe). Third, the loop may include one or both poles.
        // Note that a small clockwise loop near the equator contains both poles.
        
        // TODO: Implement RectBounder
        // For now, use a simple implementation that just takes the bounds of the vertices
        let mut lat_min = std::f64::MAX;
        let mut lat_max = std::f64::MIN;
        let mut lng_min = std::f64::MAX;
        let mut lng_max = std::f64::MIN;
        
        for v in &self.vertices {
            // Convert to lat/lng
            let lat = v.0.z.asin();
            let lng = v.0.y.atan2(v.0.x);
            
            lat_min = lat_min.min(lat);
            lat_max = lat_max.max(lat);
            lng_min = lng_min.min(lng);
            lng_max = lng_max.max(lng);
        }
        
        // Create a simple bounding rectangle
        self.bound = Rect::from_lat_lng(
            r1::Interval::new(lat_min, lat_max),
            s1::Interval::new(lng_min, lng_max)
        );
        
        // TODO: Handle poles and wrapping properly
        
        // Create the subregion bound
        self.subregion_bound = self.bound.clone();
        // TODO: Implement expand_for_subregions
    }

    /// validate checks whether this is a valid loop.
    pub fn validate(&self) -> S2Result<()> {
        self.find_validation_error_no_index()?;
    
        // Check for intersections between non-adjacent edges (including at vertices)
        // TODO: Once shapeutil gets find_any_crossing uncomment this.
        // find_any_crossing(self.index)
    
        Ok(())
    }

    /// find_validation_error_no_index reports whether this is not a valid loop, but
    /// skips checks that would require a ShapeIndex to be built for the loop. This
    /// is primarily used by Polygon to do validation so it doesn't trigger the
    /// creation of unneeded ShapeIndices.
    pub fn find_validation_error_no_index(&self) -> S2Result<()> {
        // All vertices must be unit length.
        for (i, v) in self.vertices.iter().enumerate() {
            if !v.is_unit() {
                return Err(S2Error::InvalidLoop(format!("vertex {} is not unit length", i)));
            }
        }

        // Loops must have at least 3 vertices (except for empty and full).
        if self.vertices.len() < 3 {
            if self.is_empty_or_full() {
                return Ok(()); // Skip remaining tests.
            }
            return Err(S2Error::InvalidLoop(
                "non-empty, non-full loops must have at least 3 vertices".to_string()
            ));
        }

        // Loops are not allowed to have any duplicate vertices or edge crossings.
        // We split this check into two parts. First we check that no edge is
        // degenerate (identical endpoints). Then we check that there are no
        // intersections between non-adjacent edges (including at vertices). The
        // second check needs the ShapeIndex, so it does not fall within the scope
        // of this method.
        for i in 0..self.vertices.len() {
            let v = &self.vertices[i];
            if *v == self.vertex(i as i64 + 1) {
                return Err(S2Error::InvalidLoop(
                    format!("edge {} is degenerate (duplicate vertex)", i)
                ));
            }
    
            // Antipodal vertices are not allowed.
            let other = Point(self.vertex(i as i64 + 1).0.mul(-1.0));
            if *v == other {
                return Err(S2Error::InvalidLoop(format!(
                    "vertices {} and {} are antipodal", 
                    i, (i + 1) % self.vertices.len()
                )));
            }
        }

        Ok(())
    }

/// Contains reports whether the region contained by this loop is a superset of the
/// region contained by the given other loop.
pub fn contains(&self, o: &Loop) -> bool {
    // For a loop A to contain the loop B, all of the following must
    // be true:
    //
    //  (1) There are no edge crossings between A and B except at vertices.
    //
    //  (2) At every vertex that is shared between A and B, the local edge
    //      ordering implies that A contains B.
    //
    //  (3) If there are no shared vertices, then A must contain a vertex of B
    //      and B must not contain a vertex of A. (An arbitrary vertex may be
    //      chosen in each case.)
    //
    // The second part of (3) is necessary to detect the case of two loops whose
    // union is the entire sphere, i.e. two loops that contains each other's
    // boundaries but not each other's interiors.
    if !self.subregion_bound.contains(&o.bound) {
        return false;
    }

    // Special cases to handle either loop being empty or full.
    if self.is_empty_or_full() || o.is_empty_or_full() {
        return self.is_full() || o.is_empty();
    }

    // Check whether there are any edge crossings, and also check the loop
    // relationship at any shared vertices.
    let mut relation = containsRelation { foundSharedVertex: false };
    if hasCrossingRelation(self, o, &relation) {
        return false;
    }

    // There are no crossings, and if there are any shared vertices then A
    // contains B locally at each shared vertex.
    if relation.foundSharedVertex {
        return true;
    }

    // Since there are no edge intersections or shared vertices, we just need to
    // test condition (3) above. We can skip this test if we discovered that A
    // contains at least one point of B while checking for edge crossings.
    if !self.contains_point(o.vertex(0)) {
        return false;
    }

    // We still need to check whether (A union B) is the entire sphere.
    // Normally this check is very cheap due to the bounding box precondition.
    if (o.subregion_bound.contains(&self.bound) || o.bound.union(&self.bound).is_full()) &&
        o.contains_point(self.vertex(0)) {
        return false;
    }
    
    return true;
}

/// Intersects reports whether the region contained by this loop intersects the region
/// contained by the other loop.
pub fn intersects(&self, o: &Loop) -> bool {
    // Given two loops, A and B, A.Intersects(B) if and only if !A.Complement().Contains(B).
    //
    // This code is similar to Contains, but is optimized for the case
    // where both loops enclose less than half of the sphere.
    if !self.bound.intersects(&o.bound) {
        return false;
    }

    // Check whether there are any edge crossings, and also check the loop
    // relationship at any shared vertices.
    let mut relation = intersectsRelation { foundSharedVertex: false };
    if hasCrossingRelation(self, o, &relation) {
        return true;
    }
    if relation.foundSharedVertex {
        return false;
    }

    // Since there are no edge intersections or shared vertices, the loops
    // intersect only if A contains B, B contains A, or the two loops contain
    // each other's boundaries.  These checks are usually cheap because of the
    // bounding box preconditions.  Note that neither loop is empty (because of
    // the bounding box check above), so it is safe to access vertex(0).

    // Check whether A contains B, or A and B contain each other's boundaries.
    // (Note that A contains all the vertices of B in either case.)
    if self.subregion_bound.contains(&o.bound) || self.bound.union(&o.bound).is_full() {
        if self.contains_point(o.vertex(0)) {
            return true;
        }
    }
    // Check whether B contains A.
    if o.subregion_bound.contains(&self.bound) {
        if o.contains_point(self.vertex(0)) {
            return true;
        }
    }
    return false;
}

/// Equal reports whether two loops have the same vertices in the same linear order
/// (i.e., cyclic rotations are not allowed).
pub fn equal(&self, other: &Loop) -> bool {
    if self.vertices.len() != other.vertices.len() {
        return false;
    }

    for (i, v) in self.vertices.iter().enumerate() {
        if v != &other.vertex(i as i64) {
            return false;
        }
    }
    return true;
}

/// BoundaryEqual reports whether the two loops have the same boundary. This is
/// true if and only if the loops have the same vertices in the same cyclic order
/// (i.e., the vertices may be cyclically rotated). The empty and full loops are
/// considered to have different boundaries.
pub fn boundary_equal(&self, o: &Loop) -> bool {
    if self.vertices.len() != o.vertices.len() {
        return false;
    }

    // Special case to handle empty or full loops.  Since they have the same
    // number of vertices, if one loop is empty/full then so is the other.
    if self.is_empty_or_full() {
        return self.is_empty() == o.is_empty();
    }

    // Loop through the vertices to find the first of ours that matches the
    // starting vertex of the other loop. Use that offset to then 'align' the
    // vertices for comparison.
    for (offset, vertex) in self.vertices.iter().enumerate() {
        if vertex == &o.vertex(0) {
            // There is at most one starting offset since loop vertices are unique.
            for i in 0..self.vertices.len() {
                if self.vertex((i + offset) as i64) != o.vertex(i as i64) {
                    return false;
                }
            }
            return true;
        }
    }
    return false;
}

/// compare_boundary returns +1 if this loop contains the boundary of the other loop,
/// -1 if it excludes the boundary of the other, and 0 if the boundaries of the two
/// loops cross. Shared edges are handled as follows:
///
/// If XY is a shared edge, define Reversed(XY) to be true if XY
/// appears in opposite directions in both loops.
/// Then this loop contains XY if and only if Reversed(XY) == the other loop is a hole.
/// (Intuitively, this checks whether this loop contains a vanishingly small region
/// extending from the boundary of the other toward the interior of the polygon to
/// which the other belongs.)
///
/// This function is used for testing containment and intersection of
/// multi-loop polygons. Note that this method is not symmetric, since the
/// result depends on the direction of this loop but not on the direction of
/// the other loop (in the absence of shared edges).
///
/// This requires that neither loop is empty, and if other loop is_full, then it must not
/// be a hole.
pub fn compare_boundary(&self, o: &Loop) -> i64 {
    // The bounds must intersect for containment or crossing.
    if !self.bound.intersects(&o.bound) {
        return -1;
    }

    // Full loops are handled as though the loop surrounded the entire sphere.
    if self.is_full() {
        return 1;
    }
    if o.is_full() {
        return -1;
    }

    // Check whether there are any edge crossings, and also check the loop
    // relationship at any shared vertices.
    let mut relation = new_compare_boundary_relation(o.is_hole());
    if hasCrossingRelation(self, o, &relation) {
        return 0;
    }
    if relation.foundSharedVertex {
        if relation.containsEdge { 
            return 1;
        }
    
        return -1;
    }

    // There are no edge intersections or shared vertices, so we can check
    // whether A contains an arbitrary vertex of B.
    if self.contains_point(o.vertex(0)) {
        return 1;
    }
    return -1;
}

    /// contains_origin reports true if this loop contains s2.origin_point().
    pub fn contains_origin(&self) -> bool {
        self.origin_inside
    }

    /// reference_point returns the reference point for this loop.
    pub fn reference_point(&self) -> ReferencePoint {
        origin_reference_point(self.origin_inside)
    }

// NumEdges returns the number of edges in this shape.
fn NumEdges(&mut self)-> int {
    if self.isEmptyOrFull() {
        return 0
    }
    return self.vertices.len()
}

/// Edge returns the endpoints for the given edge index.
pub fn edge(&self, i: i64) -> Edge {
    Edge { v0: self.vertex(i), v1: self.vertex(i + 1) }
}

/// NumChains reports the number of contiguous edge chains in the Loop.
pub fn num_chains(&self) -> i64 {
    if self.is_empty() {
        return 0;
    }
    return 1;
}

/// Chain returns the i-th edge chain in the Shape.
pub fn chain(&self, chain_id: i64) -> Chain {
    Chain { start: 0, length: self.num_edges() }
}

/// ChainEdge returns the j-th edge of the i-th edge chain.
pub fn chain_edge(&self, chain_id: i64, offset: i64) -> Edge {
    Edge { v0: self.vertex(offset), v1: self.vertex(offset + 1) }
}

/// ChainPosition returns a ChainPosition pair (i, j) such that edgeID is the
/// j-th edge of the Loop.
pub fn chain_position(&self, edge_id: i64) -> ChainPosition {
    ChainPosition { chain_id: 0, offset: edge_id }
}

// Dimension returns the dimension of the geometry represented by this Loop.
fn Dimension(&mut self) -> i64 { return 2 }

fn typeTag(&mut self) -> typeTag { return typeTagNone }

fn privateInterface(&mut self) {}

    /// is_empty reports true if this is the special empty loop that contains no points.
    pub fn is_empty(&self) -> bool {
        self.is_empty_or_full() && !self.contains_origin()
    }

    /// is_full reports true if this is the special full loop that contains all points.
    pub fn is_full(&self) -> bool {
        self.is_empty_or_full() && self.contains_origin()
    }

    /// is_empty_or_full reports true if this loop is either the "empty" or "full" special loops.
    pub fn is_empty_or_full(&self) -> bool {
        self.vertices.len() == 1
    }

    /// vertices returns the vertices in the loop.
    pub fn vertices(&self) -> &[Point] {
        &self.vertices
    }

    /// rect_bound returns a tight bounding rectangle. If the loop contains the point,
    /// the bound also contains it.
    pub fn rect_bound(&self) -> &Rect {
        &self.bound
    }

    /// cap_bound returns a bounding cap that may have more padding than the corresponding
    /// rect_bound. The bound is conservative such that if the loop contains a point P,
    /// the bound also contains it.
    pub fn cap_bound(&self) -> Cap {
        // TODO: Implement this properly
        Cap {
            center: self.vertices[0].clone(),
            height: 1.0,
        }
    }

    /// vertex returns the vertex for the given index. For convenience, the vertex indices
    /// wrap automatically for methods that do index math such as Edge.
    /// i.e., vertex(num_edges() + n) is the same as vertex(n).
    pub fn vertex(&self, i: i64) -> Point {
        self.vertices[(i as usize) % self.vertices.len()].clone()
    }

    /// oriented_vertex returns the vertex in reverse order if the loop represents a polygon
    /// hole. For example, arguments 0, 1, 2 are mapped to vertices n-1, n-2, n-3, where
    /// n == vertices.len(). This ensures that the interior of the polygon is always to
    /// the left of the vertex chain.
    ///
    /// This requires: 0 <= i < 2 * vertices.len()
    pub fn oriented_vertex(&self, i: i64) -> Point {
        let mut j = i - self.vertices.len() as i64;
        if j < 0 {
            j = i;
        }
        if self.is_hole() {
            j = self.vertices.len() as i64 - 1 - j;
        }
        self.vertex(j)
    }

    /// num_vertices returns the number of vertices in this loop.
    pub fn num_vertices(&self) -> usize {
        self.vertices.len()
    }

    /// brute_force_contains_point reports if the given point is contained by this loop.
    /// This method does not use the ShapeIndex, so it is only preferable below a certain
    /// size of loop.
    fn brute_force_contains_point(&self, p: Point) -> bool {
        let origin = origin_point();
        let mut inside = self.origin_inside;
        let mut crosser = ChainEdgeCrosser::new(origin, p, self.vertex(0));
        
        // Add vertex 0 twice to complete the loop
        for i in 1..=self.vertices.len() as i64 {
            inside = inside != crosser.edge_or_vertex_chain_crossing(self.vertex(i));
        }
        inside
    }

    /// contains_point returns true if the loop contains the point.
    pub fn contains_point(&self, p: Point) -> bool {
        // First check if the point is within the loop's bounding rectangle
        if !self.bound.contains_point(&p) {
            return false;
        }

        // For small loops it is faster to just check all the crossings. We also
        // use this method during loop initialization because init_origin_and_bound()
        // calls contains() before init_index(). Otherwise, we keep track of the
        // number of calls to contains() and only build the index when enough calls
        // have been made so that we think it is worth the effort.
        const MAX_BRUTE_FORCE_VERTICES: usize = 32;
        
        // TODO: Implement ShapeIndex and related functionality
        // For now, always use brute force method
        if self.index.is_none() || self.vertices.len() <= MAX_BRUTE_FORCE_VERTICES {
            return self.brute_force_contains_point(p);
        }

        // Otherwise, look up the point in the index.
        // TODO: Implement ShapeIndex iterator and related functionality
        self.brute_force_contains_point(p)
    }

/// ContainsCell reports whether the given Cell is contained by this Loop.
pub fn contains_cell(&self, target: &Cell) -> bool {
    let it = self.index.as_ref().unwrap().iterator();
    let relation = it.locate_cell_id(target.id());

    // If "target" is disjoint from all index cells, it is not contained.
    // Similarly, if "target" is subdivided into one or more index cells then it
    // is not contained, since index cells are subdivided only if they (nearly)
    // intersect a sufficient number of edges.  (But note that if "target" itself
    // is an index cell then it may be contained, since it could be a cell with
    // no edges in the loop interior.)
    if relation != Indexed {
        return false
    }

    // Otherwise check if any edges intersect "target".
    if self.boundaryApproxIntersects(it, target) {
        return false
    }

    // Otherwise check if the loop contains the center of "target".
    self.iteratorContainsPoint(it, target.Center())
}

/// IntersectsCell reports whether this Loop intersects the given cell.
pub fn intersects_cell(&self, target: &Cell) -> bool {
    let it = self.index.as_ref().unwrap().iterator();
    let relation = it.locate_cell_id(target.id());

    // If target does not overlap any index cell, there is no intersection.
    if relation == Disjoint {
        return false
    }
    // If target is subdivided into one or more index cells, there is an
    // intersection to within the ShapeIndex error bound (see Contains).
    if relation == Subdivided {
        return true
    }
    // If target is an index cell, there is an intersection because index cells
    // are created only if they have at least one edge or they are entirely
    // contained by the loop.
    if it.CellID() == target.id {
        return true
    }
    // Otherwise check if any edges intersect target.
    if self.boundaryApproxIntersects(it, target) {
        return true
    }
    // Otherwise check if the loop contains the center of target.
    return self.iteratorContainsPoint(it, target.Center())
}

/// CellUnionBound computes a covering of the Loop.
pub fn cell_union_bound(&self) -> Vec<CellID> {
    self.cap_bound().cell_union_bound()
}

/// boundary_approx_intersects reports if the loop's boundary intersects target.
/// It may also return true when the loop boundary does not intersect target but
/// some edge comes within the worst-case error tolerance.
///
/// This requires that it.locate(target) returned Indexed.
fn boundary_approx_intersects(&self, it: &ShapeIndexIterator, target: &Cell) -> bool {
    let a_clipped = it.index_cell().find_by_shape_id(0);

    // If there are no edges, there is no intersection.
    if a_clipped.edges.is_empty() {
        return false;
    }

    // We can save some work if target is the index cell itself.
    if it.cell_id() == target.id() {
        return true;
    }

    // Otherwise check whether any of the edges intersect target.
    let max_error = (FACE_CLIP_ERROR_UV_COORD + INTERSECTS_RECT_ERROR_UV_DIST);
    let bound = target.bound_uv().expanded_by_margin(max_error);
    for &ai in &a_clipped.edges {
        let (v0, v1, ok) = clip_to_padded_face(self.vertex(ai), self.vertex(ai+1), target.face(), max_error);
        if ok && edge_intersects_rect(v0, v1, bound) {
            return true;
        }
    }
    return false;
}

/// iterator_contains_point reports if the iterator that is positioned at the ShapeIndexCell
/// that may contain p, contains the point p.
fn iterator_contains_point(&self, it: &ShapeIndexIterator, p: Point) -> bool {
    // Test containment by drawing a line segment from the cell center to the
    // given point and counting edge crossings.
    let a_clipped = it.index_cell().find_by_shape_id(0);
    let mut inside = a_clipped.contains_center;
    if !a_clipped.edges.is_empty() {
        let center = it.center();
        let mut crosser = EdgeCrosser::new(center, p);
        let mut ai_prev = -2;
        for &ai in &a_clipped.edges {
            if ai != ai_prev + 1 {
                crosser.restart_at(self.vertex(ai));
            }
            ai_prev = ai;
            inside = inside != crosser.edge_or_vertex_chain_crossing(self.vertex(ai + 1));
        }
    }
    return inside;
}

/// regular_loop creates a loop with the given number of vertices, all
/// located on a circle of the specified radius around the given center.
pub fn regular_loop(center: Point, radius: Angle, num_vertices: i64) -> Loop {
    regular_loop_for_frame(get_frame(center), radius, num_vertices)
}

/// regular_loop_for_frame creates a loop centered around the z-axis of the given
/// coordinate frame, with the first vertex in the direction of the positive x-axis.
pub fn regular_loop_for_frame(frame: Matrix3<f64>, radius: Angle, num_vertices: i64) -> Loop {
    Loop::from_points(&regular_points_for_frame(frame, radius, num_vertices))
}

/// canonical_first_vertex returns a first index and a direction (either +1 or -1)
/// such that the vertex sequence (first, first+dir, ..., first+(n-1)*dir) does
/// not change when the loop vertex order is rotated or inverted. This allows the
/// loop vertices to be traversed in a canonical order. The return values are
/// chosen such that (first, ..., first+n*dir) are in the range [0, 2*n-1] as
/// expected by the vertex method.
pub fn canonical_first_vertex(&self) -> (i64, i64) {
    let mut first_idx = 0;
    let n = self.vertices.len() as i64;
    for i in 1..n {
        if self.vertex(i).cmp(&self.vertex(first_idx).0) == Ordering::Less {
            first_idx = i;
        }
    }

    // 0 <= first_idx <= n-1, so (first_idx+n*dir) <= 2*n-1.
    if self.vertex(first_idx + 1).cmp(&self.vertex(first_idx + n - 1).0) == Ordering::Less {
        return (first_idx, 1);
    }

    // n <= first_idx <= 2*n-1, so (first_idx+n*dir) >= 0.
    first_idx += n;
    return (first_idx, -1);
}

/// turning_angle returns the sum of the turning angles at each vertex. The return
/// value is positive if the loop is counter-clockwise, negative if the loop is
/// clockwise, and zero if the loop is a great circle. Degenerate and
/// nearly-degenerate loops are handled consistently with sign. So for example,
/// if a loop has zero area (i.e., it is a very small CCW loop) then the turning
/// angle will always be negative.
///
/// This quantity is also called the "geodesic curvature" of the loop.
pub fn turning_angle(&self) -> f64 {
    // For empty and full loops, we return the limit value as the loop area
    // approaches 0 or 4*Pi respectively.
    if self.is_empty_or_full() {
    if self.ContainsOrigin() {
    return - 2 * math.Pi
    }
    return 2 * math.Pi
    }

    // Don't crash even if the loop is not well-defined.
    if self.vertices.len() < 3 {
    return 0
    }

    // To ensure that we get the same result when the vertex order is rotated,
    // and that the result is negated when the vertex order is reversed, we need
    // to add up the individual turn angles in a consistent order. (In general,
    // adding up a set of numbers in a different order can change the sum due to
    // rounding errors.)
    //
    // Furthermore, if we just accumulate an ordinary sum then the worst-case
    // error is quadratic in the number of vertices. (This can happen with
    // spiral shapes, where the partial sum of the turning angles can be linear
    // in the number of vertices.) To avoid this we use the Kahan summation
    // algorithm (http://en.wikipedia.org/wiki/Kahan_summation_algorithm).
    let n_vertices = self.vertices.len() as i64;
    let (mut i, dir) = self.canonical_first_vertex();
    let mut sum = turn_angle(
        self.vertex((i + n_vertices - dir) % n_vertices), 
        self.vertex(i), 
        self.vertex((i + dir) % n_vertices)
    );

    let mut compensation = Angle(0.0);
    let mut n = n_vertices - 1;
    while n > 0 {
        i += dir;
        let angle = turn_angle(
            self.vertex(i - dir), 
            self.vertex(i), 
            self.vertex(i + dir)
        );
        let old_sum = sum;
        let adjusted_angle = angle + compensation;
        sum += adjusted_angle;
        compensation = (old_sum - sum) + adjusted_angle;
        n -= 1;
    }

    const MAX_CURVATURE: f64 = 2.0 * PI - 4.0 * DBL_EPSILON;

    f64::max(-MAX_CURVATURE, f64::min(MAX_CURVATURE, dir as f64 * (sum + compensation) as f64))
}

/// turning_angle_max_error return the maximum error in turning_angle. The value is not
/// constant; it depends on the loop.
pub fn turning_angle_max_error(&self) -> f64 {
    // The maximum error can be bounded as follows:
    //   3.00 * dblEpsilon    for RobustCrossProd(b, a)
    //   3.00 * dblEpsilon    for RobustCrossProd(c, b)
    //   3.25 * dblEpsilon    for Angle()
    //   2.00 * dblEpsilon    for each addition in the Kahan summation
    //   ------------------
    //  11.25 * dblEpsilon
    let max_error_per_vertex = 11.25 * DBL_EPSILON;
    max_error_per_vertex * self.vertices.len() as f64
}

    /// is_hole reports whether this loop represents a hole in its containing polygon.
    pub fn is_hole(&self) -> bool { 
        (self.depth & 1) != 0 
    }

    /// sign returns -1 if this Loop represents a hole in its containing polygon, and +1 otherwise.
    pub fn sign(&self) -> i64 {
        if self.is_hole() {
            -1
        } else {
            1
        }
    }

/// is_normalized reports whether the loop area is at most 2*pi. Degenerate loops are
/// handled consistently with sign, i.e., if a loop can be
/// expressed as the union of degenerate or nearly-degenerate CCW triangles,
/// then it will always be considered normalized.
pub fn is_normalized(&self) -> bool {
    // Optimization: if the longitude span is less than 180 degrees, then the
    // loop covers less than half the sphere and is therefore normalized.
    if self.bound.lng.length() < PI {
        return true;
    }

    // We allow some error so that hemispheres are always considered normalized.
    // TODO(roberts): This is no longer required by the Polygon implementation,
    // so alternatively we could create the invariant that a loop is normalized
    // if and only if its complement is not normalized.
    self.turning_angle() >= -self.turning_angle_max_error()
}

/// normalize inverts the loop if necessary so that the area enclosed by the loop
/// is at most 2*pi.
pub fn normalize(&mut self) {
    if !self.is_normalized() {
        self.invert();
    }
}

/// invert reverses the order of the loop vertices, effectively complementing the
/// region represented by the loop. For example, the loop ABCD (with edges
/// AB, BC, CD, DA) becomes the loop DCBA (with edges DC, CB, BA, AD).
/// Notice that the last edge is the same in both cases except that its
/// direction has been reversed.
pub fn invert(&mut self) {
    if let Some(index) = &mut self.index {
        index.reset();
    }
    
    if self.is_empty_or_full() {
        if self.is_full() {
            self.vertices[0] = EMPTY_LOOP_POINT.clone();
        } else {
            self.vertices[0] = FULL_LOOP_POINT.clone();
        }
    } else {
        // For non-special loops, reverse the slice of vertices.
        let len = self.vertices.len();
        for i in 0..(len / 2) {
            let opp = len - 1 - i;
            self.vertices.swap(i, opp);
        }
    }

    // origin_inside must be set correctly before building the ShapeIndex.
    self.origin_inside = !self.origin_inside;
    if self.bound.lat.lo > -PI / 2.0 && self.bound.lat.hi < PI / 2.0 {
        // The complement of this loop contains both poles.
        self.bound = Rect::full();
        self.subregion_bound = self.bound.clone();
    } else {
        self.init_bound();
    }
    
    if let Some(index) = &mut self.index {
        index.add(self);
    }
}

/// find_vertex returns the index of the vertex at the given Point in the range
/// 1..num_vertices, and a boolean indicating if a vertex was found.
fn find_vertex(&self, p: Point) -> (i64, bool) {
    const NOT_FOUND: i64 = 0;
    if self.vertices.len() < 10 {
        // Exhaustive search for loops below a small threshold.
        for i in 1..=self.vertices.len() {
            if self.vertex(i as i64) == p {
                return (i as i64, true);
            }
        }
        return (NOT_FOUND, false);
    }

    if let Some(index) = &self.index {
        let it = index.iterator();
        if !it.locate_point(p) {
            return (NOT_FOUND, false);
        }

        let a_clipped = it.index_cell().find_by_shape_id(0);
        for i in (0..a_clipped.num_edges()).rev() {
            let ai = a_clipped.edges[i];
            if self.vertex(ai) == p {
                if ai == 0 {
                    return (self.vertices.len() as i64, true);
                }
                return (ai, true);
            }

            if self.vertex(ai + 1) == p {
                return (ai + 1, true);
            }
        }
    }
    return (NOT_FOUND, false);
}

/// contains_nested reports whether the given loops is contained within this loop.
/// This function does not test for edge intersections. The two loops must meet
/// all of the Polygon requirements; for example this implies that their
/// boundaries may not cross or have any shared edges (although they may have
/// shared vertices).
pub fn contains_nested(&self, other: &Loop) -> bool {
    if !self.subregion_bound.contains(&other.bound) {
        return false;
    }

    // Special cases to handle either loop being empty or full.  Also bail out
    // when B has no vertices to avoid heap overflow on the vertex(1) call
    // below.  (This method is called during polygon initialization before the
    // client has an opportunity to call is_valid().)
    if self.is_empty_or_full() || other.num_vertices() < 2 {
        return self.is_full() || other.is_empty();
    }

    // We are given that A and B do not share any edges, and that either one
    // loop contains the other or they do not intersect.
    let (m, ok) = self.find_vertex(other.vertex(1));
    if !ok {
        // Since other.vertex(1) is not shared, we can check whether A contains it.
        return self.contains_point(other.vertex(1));
    }

    // Check whether the edge order around other.Vertex(1) is compatible with
    // A containing B.
    wedge_contains(
        self.vertex(m - 1), 
        self.vertex(m), 
        self.vertex(m + 1), 
        other.vertex(0), 
        other.vertex(2)
    )
}

/// surface_integral_float64 computes the oriented surface integral of some quantity f(x)
/// over the loop interior, given a function f(A,B,C) that returns the
/// corresponding integral over the spherical triangle ABC. Here "oriented
/// surface integral" means:
///
/// (1) f(A,B,C) must be the integral of f if ABC is counterclockwise,
///
/// and the integral of -f if ABC is clockwise.
///
/// (2) The result of this function is *either* the integral of f over the
///
/// loop interior, or the integral of (-f) over the loop exterior.
///
/// Note that there are at least two common situations where it easy to work
/// around property (2) above:
///
///   - If the integral of f over the entire sphere is zero, then it doesn't
///     matter which case is returned because they are always equal.
///
///   - If f is non-negative, then it is easy to detect when the integral over
///     the loop exterior has been returned, and the integral over the loop
///     interior can be obtained by adding the integral of f over the entire
///     unit sphere (a constant) to the result.
///
/// Any changes to this method may need corresponding changes to surface_integral_point as well.
pub fn surface_integral_float64<F>(&self, f: F) -> f64 
where 
    F: Fn(&Point, &Point, &Point) -> f64
{
    // We sum f over a collection T of oriented triangles, possibly
    // overlapping. Let the sign of a triangle be +1 if it is CCW and -1
    // otherwise, and let the sign of a point x be the sum of the signs of the
    // triangles containing x. Then the collection of triangles T is chosen
    // such that either:
    //
    //  (1) Each point in the loop interior has sign +1, and sign 0 otherwise; or
    //  (2) Each point in the loop exterior has sign -1, and sign 0 otherwise.
    //
    // The triangles basically consist of a fan from vertex 0 to every loop
    // edge that does not include vertex 0. These triangles will always satisfy
    // either (1) or (2). However, what makes this a bit tricky is that
    // spherical edges become numerically unstable as their length approaches
    // 180 degrees. Of course there is not much we can do if the loop itself
    // contains such edges, but we would like to make sure that all the triangle
    // edges under our control (i.e., the non-loop edges) are stable. For
    // example, consider a loop around the equator consisting of four equally
    // spaced points. This is a well-defined loop, but we cannot just split it
    // into two triangles by connecting vertex 0 to vertex 2.
    //
    // We handle this type of situation by moving the origin of the triangle fan
    // whenever we are about to create an unstable edge. We choose a new
    // location for the origin such that all relevant edges are stable. We also
    // create extra triangles with the appropriate orientation so that the sum
    // of the triangle signs is still correct at every point.

    // The maximum length of an edge for it to be considered numerically stable.
    // The exact value is fairly arbitrary since it depends on the stability of
    // the function f. The value below is quite conservative but could be
    // reduced further if desired.
    const MAX_LENGTH: f64 = PI - 1e-5;

    let mut sum = 0.0;
    let mut origin = self.vertex(0);
    for i in 1..self.vertices.len() as i64 - 1 {
        // Let V_i be vertex(i), let O be the current origin, and let length(A,B)
        // be the length of edge (A,B). At the start of each loop iteration, the
        // "leading edge" of the triangle fan is (O,V_i), and we want to extend
        // the triangle fan so that the leading edge is (O,V_i+1).
        //
        // Invariants:
        //  1. length(O,V_i) < MAX_LENGTH for all (i > 1).
        //  2. Either O == V_0, or O is approximately perpendicular to V_0.
        //  3. "sum" is the oriented integral of f over the area defined by
        //     (O, V_0, V_1, ..., V_i).
        if self.vertex(i + 1).angle(&origin.0) > MAX_LENGTH {
            // We are about to create an unstable edge, so choose a new origin O'
            // for the triangle fan.
            let old_origin = origin;
            if origin == self.vertex(0) {
                // The following point is well-separated from V_i and V_0 (and
                // therefore V_i+1 as well).
                origin = Point(self.vertex(0).point_cross(&self.vertex(i)).normalize());
            } else if self.vertex(i).angle(&self.vertex(0).0) < MAX_LENGTH {
                // All edges of the triangle (O, V_0, V_i) are stable, so we can
                // revert to using V_0 as the origin.
                origin = self.vertex(0);
            } else {
                // (O, V_i+1) and (V_0, V_i) are antipodal pairs, and O and V_0 are
                // perpendicular. Therefore V_0.cross(O) is approximately
                // perpendicular to all of {O, V_0, V_i, V_i+1}, and we can choose
                // this point O' as the new origin.
                origin = Point(self.vertex(0).cross(&old_origin.0));

                // Advance the edge (V_0,O) to (V_0,O').
                sum += f(&self.vertex(0), &old_origin, &origin);
            }
            // Advance the edge (O,V_i) to (O',V_i).
            sum += f(&old_origin, &self.vertex(i), &origin);
        }
        // Advance the edge (O,V_i) to (O,V_i+1).
        sum += f(&origin, &self.vertex(i), &self.vertex(i + 1));
    }
    // If the origin is not V_0, we need to sum one more triangle.
    if origin != self.vertex(0) {
        // Advance the edge (O,V_n-1) to (O,V_0).
        sum += f(&origin, &self.vertex(self.vertices.len() as i64 - 1), &self.vertex(0));
    }
    return sum;
}

/// surface_integral_point mirrors the surface_integral_float64 method but over Points;
/// see that method for commentary. The C++ version uses a templated method.
/// Any changes to this method may need corresponding changes to surface_integral_float64 as well.
pub fn surface_integral_point<F>(&self, f: F) -> Point 
where 
    F: Fn(&Point, &Point, &Point) -> Point
{
    const MAX_LENGTH: f64 = PI - 1e-5;
    let mut sum = Vector { x: 0.0, y: 0.0, z: 0.0 };

    let mut origin = self.vertex(0);
    for i in 1..self.vertices.len() as i64 - 1 {
        if self.vertex(i + 1).angle(&origin.0) > MAX_LENGTH {
            let old_origin = origin;
            if origin == self.vertex(0) {
                origin = Point(self.vertex(0).point_cross(&self.vertex(i)).normalize());
            } else if self.vertex(i).angle(&self.vertex(0).0) < MAX_LENGTH {
                origin = self.vertex(0);
            } else {
                origin = Point(self.vertex(0).cross(&old_origin.0));
                sum = sum.add(f(&self.vertex(0), &old_origin, &origin).0);
            }
            sum = sum.add(f(&old_origin, &self.vertex(i), &origin).0);
        }
        sum = sum.add(f(&origin, &self.vertex(i), &self.vertex(i + 1)).0);
    }
    if origin != self.vertex(0) {
        sum = sum.add(f(&origin, &self.vertex(self.vertices.len() as i64 - 1), &self.vertex(0)).0);
    }
    Point(sum)
}

/// area returns the area of the loop interior, i.e. the region on the left side of
/// the loop. The return value is between 0 and 4*pi. (Note that the return
/// value is not affected by whether this loop is a "hole" or a "shell".)
pub fn area(&self) -> f64 {
    // It is surprisingly difficult to compute the area of a loop robustly. The
    // main issues are (1) whether degenerate loops are considered to be CCW or
    // not (i.e., whether their area is close to 0 or 4*pi), and (2) computing
    // the areas of small loops with good relative accuracy.
    //
    // With respect to degeneracies, we would like Area to be consistent
    // with contains_point in that loops that contain many points
    // should have large areas, and loops that contain few points should have
    // small areas. For example, if a degenerate triangle is considered CCW
    // according to s2predicates Sign, then it will contain very few points and
    // its area should be approximately zero. On the other hand if it is
    // considered clockwise, then it will contain virtually all points and so
    // its area should be approximately 4*pi.
    //
    // More precisely, let U be the set of Points for which is_unit_length
    // is true, let P(U) be the projection of those points onto the mathematical
    // unit sphere, and let V(P(U)) be the Voronoi diagram of the projected
    // points. Then for every loop x, we would like Area to approximately
    // equal the sum of the areas of the Voronoi regions of the points p for
    // which x.contains_point(p) is true.
    //
    // The second issue is that we want to compute the area of small loops
    // accurately. This requires having good relative precision rather than
    // good absolute precision. For example, if the area of a loop is 1e-12 and
    // the error is 1e-15, then the area only has 3 digits of accuracy. (For
    // reference, 1e-12 is about 40 square meters on the surface of the earth.)
    // We would like to have good relative accuracy even for small loops.
    //
    // To achieve these goals, we combine two different methods of computing the
    // area. This first method is based on the Gauss-Bonnet theorem, which says
    // that the area enclosed by the loop equals 2*pi minus the total geodesic
    // curvature of the loop (i.e., the sum of the "turning angles" at all the
    // loop vertices). The big advantage of this method is that as long as we
    // use Sign to compute the turning angle at each vertex, then
    // degeneracies are always handled correctly. In other words, if a
    // degenerate loop is CCW according to the symbolic perturbations used by
    // Sign, then its turning angle will be approximately 2*pi.
    //
    // The disadvantage of the Gauss-Bonnet method is that its absolute error is
    // about 2e-15 times the number of vertices (see turning_angle_max_error).
    // So, it cannot compute the area of small loops accurately.
    //
    // The second method is based on splitting the loop into triangles and
    // summing the area of each triangle. To avoid the difficulty and expense
    // of decomposing the loop into a union of non-overlapping triangles,
    // instead we compute a signed sum over triangles that may overlap (see the
    // comments for surface_integral). The advantage of this method
    // is that the area of each triangle can be computed with much better
    // relative accuracy (using l'Huilier's theorem). The disadvantage is that
    // the result is a signed area: CCW loops may yield a small positive value,
    // while CW loops may yield a small negative value (which is converted to a
    // positive area by adding 4*pi). This means that small errors in computing
    // the signed area may translate into a very large error in the result (if
    // the sign of the sum is incorrect).
    //
    // So, our strategy is to combine these two methods as follows. First we
    // compute the area using the "signed sum over triangles" approach (since it
    // is generally more accurate). We also estimate the maximum error in this
    // result. If the signed area is too close to zero (i.e., zero is within
    // the error bounds), then we double-check the sign of the result using the
    // Gauss-Bonnet method. (In fact we just call is_normalized, which is
    // based on this method.) If the two methods disagree, we return either 0
    // or 4*pi based on the result of is_normalized. Otherwise we return the
    // area that we computed originally.
    if self.is_empty_or_full() {
        if self.contains_origin() {
            return 4.0 * PI;
        }
        return 0.0;
    }
    area = self.surfaceIntegralFloat64(SignedArea)

    // TODO(roberts): This error estimate is very approximate. There are two
    // issues: (1) SignedArea needs some improvements to ensure that its error
    // is actually never higher than GirardArea, and (2) although the number of
    // triangles in the sum is typically N-2, in theory it could be as high as
    // 2*N for pathological inputs. But in other respects this error bound is
    // very conservative since it assumes that the maximum error is achieved on
    // every triangle.
    maxError = self.turningAngleMaxError()

    let area = self.surface_integral_float64(signed_area);

    // TODO(roberts): This error estimate is very approximate. There are two
    // issues: (1) SignedArea needs some improvements to ensure that its error
    // is actually never higher than GirardArea, and (2) although the number of
    // triangles in the sum is typically N-2, in theory it could be as high as
    // 2*N for pathological inputs. But in other respects this error bound is
    // very conservative since it assumes that the maximum error is achieved on
    // every triangle.
    let max_error = self.turning_angle_max_error();

    // The signed area should be between approximately -4*pi and 4*pi.
    let mut area = if area < 0.0 {
        // We have computed the negative of the area of the loop exterior.
        area + 4.0 * PI
    } else {
        area
    };

    if area > 4.0 * PI {
        area = 4.0 * PI;
    }
    if area < 0.0 {
        area = 0.0;
    }

    // If the area is close enough to zero or 4*pi so that the loop orientation
    // is ambiguous, then we compute the loop orientation explicitly.
    if area < max_error && !self.is_normalized() {
        return 4.0 * PI;
    } else if area > (4.0 * PI - max_error) && self.is_normalized() {
        return 0.0;
    }

    return area
}

/// centroid returns the true centroid of the loop multiplied by the area of the
/// loop. The result is not unit length, so you may want to normalize it. Also
/// note that in general, the centroid may not be contained by the loop.
///
/// We prescale by the loop area for two reasons: (1) it is cheaper to
/// compute this way, and (2) it makes it easier to compute the centroid of
/// more complicated shapes (by splitting them into disjoint regions and
/// adding their centroids).
///
/// Note that the return value is not affected by whether this loop is a
/// "hole" or a "shell".
pub fn centroid(&self) -> Point {
    // surface_integral_point() returns either the integral of position over loop
    // interior, or the negative of the integral of position over the loop
    // exterior. But these two values are the same (!), because the integral of
    // position over the entire sphere is (0, 0, 0).
    self.surface_integral_point(true_centroid)
}

// Encode encodes the Loop.
// fn Encode(&mut self, w io.Writer) -> error {
//     e = & encoder{w: w}
//     self.encode(e)
//     return e.err
// }
// 
// fn  encode(&mut self, e *encoder) {
//     e.writeInt8(encodingVersion)
//     e.writeUint32(uint32(self.vertices)).len()
//     for _, v= range self.vertices {
//     e.writeFloat64(v.X)
//     e.writeFloat64(v.Y)
//     e.writeFloat64(v.Z)
//     }
// 
//     e.writeBool(self.origin_inside)
//     e.writeInt32(int32(self.depth))
// 
//     // Encode the bound.
//     self.bound.encode(e)
// }
// 
// // Decode decodes a loop.
// fn Decode(&mut self, r io.Reader) -> error {
//     * l = Loop{}
//     d= & decoder{r: asByteReader(r)}
//     self.decode(d)
//     return d.err
// }
// 
// fn decode(&mut self, d *decoder) {
//     version= int8(d.readUint8())
//     if d.err != nil {
//     return
//     }
//     if version != encodingVersion {
//     d.err = fmt.Errorf("cannot decode version %d", version)
//     return
//     }
// 
//     // Empty loops are explicitly allowed here: a newly created loop has zero vertices
//     // and such loops encode and decode properly.
//     nvertices= d.readUint32()
//     if nvertices > maxEncodedVertices {
//     if d.err == nil {
//     d.err = fmt.Errorf("too many vertices (%d; max is %d)", nvertices, maxEncodedVertices)
// 
//     }
//     return
//     }
//     self.vertices = make([]Point, nvertices)
//     for i= range self.vertices {
//     self.vertices[i].X = d.readFloat64()
//     self.vertices[i].Y = d.readFloat64()
//     self.vertices[i].Z = d.readFloat64()
//     }
//     self.index = NewShapeIndex()
//     self.origin_inside = d.readBool()
//     self.depth = int(d.readUint32())
//     self.bound.decode(d)
//     self.subregion_bound = ExpandForSubregions(self.bound)
// 
//     self.index.Add(l)
// }
// 
// // Bitmasks to read from properties.
// const (
// origin_inside = 1 < < iota
// boundEncoded
// )
// 
// fn xyzFaceSiTiVertices(&mut self) -> []xyzFaceSiTi {
//     ret = make([]xyzFaceSiTi, self.vertices).len()
//     for i, v = range self.vertices {
//     ret[i].xyz = v
//     ret[i].face, ret[i].si, ret[i].ti, ret[i].level = xyzToFaceSiTi(v)
//     }
//     return ret
// }
// 
// fn encodeCompressed(&mut self, e *encoder, snapLevel int, vertices []xyzFaceSiTi) {
//     if self.vertices) != len(vertices.len() {
//     panic("encodeCompressed: vertices must be the same length as self.vertices")
//     }
//     if vertices.len() > maxEncodedVertices {
//     if e.err == nil {
//     e.err = fmt.Errorf("too many vertices (%d; max is %d)", vertices), maxEncodedVertices.len()
//     }
//     return
//     }
//     e.writeUvarint(uint64(vertices)).len()
//     encodePointsCompressed(e, vertices, snapLevel)
// 
//     props= self.compressedEncodingProperties()
//     e.writeUvarint(props)
//     e.writeUvarint(uint64(self.depth))
//     if props & boundEncoded != 0 {
//     self.bound.encode(e)
//     }
// }
// 
// fn compressedEncodingProperties(&mut self) -> uint64 {
//     var properties uint64
//     if self.origin_inside {
//     properties |= origin_inside
//     }
// 
//     // Write whether there is a bound so we can change the threshold later.
//     // Recomputing the bound multiplies the decode time taken per vertex
//     // by a factor of about 3.5.  Without recomputing the bound, decode
//     // takes approximately 125 ns / vertex.  A loop with 63 vertices
//     // encoded without the bound will take ~30us to decode, which is
//     // acceptable.  At ~3.5 bytes / vertex without the bound, adding
//     // the bound will increase the size by <15%, which is also acceptable.
//     const minVerticesForBound = 64
//     if self.vertices.len() > = minVerticesForBound {
//     properties |= boundEncoded
//     }
// 
//     return properties
// }
// 
// fn decodeCompressed(&mut self, d *decoder, snapLevel int) {
//     nvertices= d.readUvarint()
//     if d.err != nil {
//     return
//     }
//     if nvertices > maxEncodedVertices {
//     d.err = fmt.Errorf("too many vertices (%d; max is %d)", nvertices, maxEncodedVertices)
//     return
//     }
//     self.vertices = make([]Point, nvertices)
//     decodePointsCompressed(d, snapLevel, self.vertices)
//     properties= d.readUvarint()
// 
//     // Make sure values are valid before using.
//     if d.err != nil {
//     return
//     }
// 
//     self.index = NewShapeIndex()
//     self.origin_inside = (properties & origin_inside) != 0
// 
//     self.depth = int(d.readUvarint())
// 
//     if (properties & boundEncoded) != 0 {
//     self.bound.decode(d)
//     if d.err != nil {
//     return
//     }
//     self.subregion_bound = ExpandForSubregions(self.bound)
//     } else {
//     self.initBound()
//     }
// 
//     self.index.Add(l)
// }
// 

/// contains_non_crossing_boundary reports whether given two loops whose boundaries
/// do not cross (see compare_boundary), if this loop contains the boundary of the
/// other loop. If reverse is true, the boundary of the other loop is reversed
/// first (which only affects the result when there are shared edges). This method
/// is cheaper than compare_boundary because it does not test for edge intersections.
///
/// This function requires that neither loop is empty, and that if the other is full,
/// then reverse == false.
pub fn contains_non_crossing_boundary(&self, other: &Loop, reverse_other: bool) -> bool {
    // The bounds must intersect for containment.
    if !self.bound.intersects(&other.bound) {
        return false;
    }

    // Full loops are handled as though the loop surrounded the entire sphere.
    if self.is_full() {
        return true;
    }
    if other.is_full() {
        return false;
    }

    let (m, ok) = self.find_vertex(other.vertex(0));
    if !ok {
        // Since the other loops vertex 0 is not shared, we can check if this contains it.
        return self.contains_point(other.vertex(0));
    }
    // Otherwise check whether the edge (b0, b1) is contained by this loop.
    wedge_contains_semiwedge(
        &self.vertex(m-1), 
        &self.vertex(m), 
        &self.vertex(m+1),
        &other.vertex(1), 
        reverse_other
    )
}
/// CrossingTarget is an enum representing the possible crossing target cases for relations.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CrossingTarget {
    DontCare,
    DontCross,
    Cross,
}

/// LoopRelation defines the interface for checking a type of relationship between two loops.
/// Some examples of relations are Contains, Intersects, or CompareBoundary.
pub trait LoopRelation {
    /// Optionally, a_crossing_target and b_crossing_target can specify an early-exit
    /// condition for the loop relation. If any point P is found such that
    ///
    ///   A.contains_point(P) == a_crossing_target() &&
    ///   B.contains_point(P) == b_crossing_target()
    ///
    /// then the loop relation is assumed to be the same as if a pair of crossing
    /// edges were found. For example, the contains_point relation has
    ///
    ///   a_crossing_target() == CrossingTarget::DontCross
    ///   b_crossing_target() == CrossingTarget::Cross
    ///
    /// because if A.contains_point(P) == false and B.contains_point(P) == true
    /// for any point P, then it is equivalent to finding an edge crossing (i.e.,
    /// since Contains returns false in both cases).
    ///
    /// Loop relations that do not have an early-exit condition of this form
    /// should return CrossingTarget::DontCare for both crossing targets.

    /// a_crossing_target reports whether loop A crosses the target point with
    /// the given relation type.
    fn a_crossing_target(&self) -> CrossingTarget;
    
    /// b_crossing_target reports whether loop B crosses the target point with
    /// the given relation type.
    fn b_crossing_target(&self) -> CrossingTarget;

    /// wedges_cross reports if a shared vertex ab1 and the two associated wedges
    /// (a0, ab1, b2) and (b0, ab1, b2) are equivalent to an edge crossing.
    /// The loop relation is also allowed to maintain its own internal state, and
    /// can return true if it observes any sequence of wedges that are equivalent
    /// to an edge crossing.
    fn wedges_cross(&mut self, a0: &Point, ab1: &Point, a2: &Point, b0: &Point, b2: &Point) -> bool;
}

/// LoopCrosser is a helper type for determining whether two loops cross.
/// It is instantiated twice for each pair of loops to be tested, once for the
/// pair (A,B) and once for the pair (B,A), in order to be able to process
/// edges in either loop nesting order.
pub struct LoopCrosser<'a> {
    a: &'a Loop,
    b: &'a Loop,
    relation: &'a mut dyn LoopRelation,
    swapped: bool,
    a_crossing_target: CrossingTarget,
    b_crossing_target: CrossingTarget,

    // state maintained by start_edge and edge_crosses_cell.
    crosser: Option<EdgeCrosser>,
    aj: i64,
    bj_prev: i64,

    // temporary data declared here to avoid repeated memory allocations.
    b_query: CrossingEdgeQuery,
    b_cells: Vec<ShapeIndexCell>,
}
impl<'a> LoopCrosser<'a> {
    /// new_loop_crosser creates a LoopCrosser from the given values. If swapped is true,
    /// the loops A and B have been swapped. This affects how arguments are passed to
    /// the given loop relation, since for example A.contains(B) is not the same as
    /// B.contains(A).
    pub fn new(a: &'a Loop, b: &'a Loop, relation: &'a mut dyn LoopRelation, swapped: bool) -> Self {
        let a_crossing_target = relation.a_crossing_target();
        let b_crossing_target = relation.b_crossing_target();
        
        let mut crosser = LoopCrosser {
            a,
            b,
            relation,
            swapped,
            a_crossing_target,
            b_crossing_target,
            crosser: None,
            aj: 0,
            bj_prev: -2,
            b_query: CrossingEdgeQuery::new(b.index.as_ref().unwrap()),
            b_cells: Vec::new(),
        };
        
        if swapped {
            std::mem::swap(&mut crosser.a_crossing_target, &mut crosser.b_crossing_target);
        }

        crosser
    }

    // startEdge sets the crossers state for checking the given edge of loop A.
    fn startEdge(&mut self, aj: i64) {
        self.crosser = NewEdgeCrosser( self.a.Vertex(aj), self.a.Vertex(aj + 1))
        self.aj = aj
        self.bjPrev = - 2
    }

    // edgeCrossesCell reports whether the current edge of loop A has any crossings with
    // edges of the index cell of loop B.
    fn edgeCrossesCell(&mut self, bClipped *clippedShape) -> bool {
        // Test the current edge of A against all edges of bClipped
        bNumEdges = bClipped.numEdges()
        for j = 0; j < bNumEdges; j++ {
        bj = bClipped.edges[j]
        if bj != self.bjPrev + 1 {
        self.crosser.RestartAt( self.b.Vertex(bj))
        }
        self.bjPrev = bj
        if crossing = self.crosser.ChainCrossingSign( self.b.Vertex(bj + 1)); crossing == DoNotCross {
        continue
        } else if crossing == Cross {
        return true
        }
    
        // We only need to check each shared vertex once, so we only
        // consider the case where self.aVertex(self.aj+1) == self.b.Vertex(bj+1).
        if self.a.Vertex( self.aj+ 1) == self.b.Vertex(bj + 1) {
        if self.swapped {
        if self.relation.wedgesCross( self.b.Vertex(bj), self.b.Vertex(bj + 1), self.b.Vertex(bj + 2), self.a.Vertex( self.aj), self.a.Vertex( self.aj + 2)) {
        return true
        }
        } else {
        if self.relation.wedgesCross( self.a.Vertex( self.aj), self.a.Vertex( self.aj + 1), self.a.Vertex( self.aj+ 2), self.b.Vertex(bj), self.b.Vertex(bj+ 2)) {
        return true
        }
        }
        }
        }
    
        return false
    }

    // cellCrossesCell reports whether there are any edge crossings or wedge crossings
    // within the two given cells.
    fn cellCrossesCell(&mut self, aClipped: &clippedShape, bClipped: &clippedShape) -> bool {
        // Test all edges of aClipped against all edges of bClipped.
        for _, edge = range aClipped.edges {
        self .startEdge(edge)
        if self .edgeCrossesCell(bClipped) {
        return true
        }
        }
    
        return false
    }

    // cellCrossesAnySubcell reports whether given an index cell of A, if there are any
    // edge or wedge crossings with any index cell of B contained within bID.
    fn cellCrossesAnySubcell(&mut self, aClipped: *clippedShape, bID: CellID) -> bool {
        // Test all edges of aClipped against all edges of B. The relevant B
        // edges are guaranteed to be children of bID, which lets us find the
        // correct index cells more efficiently.
        bRoot = PaddedCellFromCellID(bID, 0)
        for _, aj = range aClipped.edges {
        // Use an CrossingEdgeQuery starting at bRoot to find the index cells
        // of B that might contain crossing edges.
        self .bCells = self .bQuery.getCells( self .a.Vertex(aj), self .a.Vertex(aj+1), bRoot)
        if  self .bCells.len() == 0 {
        continue
        }
        self .startEdge(aj)
        for c = 0; c <  self .bCells.len(); c++ {
        if self.edgeCrossesCell( self.bCells[c].shapes[0]) {
        return true
        }
        }
        }
    
        return false
    }

    // hasCrossing reports whether given two iterators positioned such that
    // ai.cellID().ContainsCellID(bi.cellID()), there is an edge or wedge crossing
    // anywhere within ai.cellID(). This fntion advances bi only past ai.cellID().
    fn hasCrossing(&mut self, ai: &rangeIterator, bi: &rangeIterator) -> bool {
        // If ai.CellID() intersects many edges of B, then it is faster to use
        // CrossingEdgeQuery to narrow down the candidates. But if it intersects
        // only a few edges, it is faster to check all the crossings directly.
        // We handle this by advancing bi and keeping track of how many edges we
        // would need to test.
        const edgeQueryMinEdges = 20 // Tuned from benchmarks.
        var totalEdges int
        self .bCells = nil
    
        for {
        if n = bi.it.IndexCell().shapes[0].numEdges(); n > 0 {
        totalEdges += n
        if totalEdges > = edgeQueryMinEdges {
        // There are too many edges to test them directly, so use CrossingEdgeQuery.
        if self.cellCrossesAnySubcell(ai.it.IndexCell().shapes[0], ai.cellID()) {
        return true
        }
        bi.seekBeyond(ai)
        return false
        }
        self.bCells = append( self.bCells, bi.indexCell())
        }
        bi.next()
        if bi.cellID() > ai.rangeMax {
        break
        }
        }
    
        // Test all the edge crossings directly.
        for _, c = range self .bCells {
        if self.cellCrossesCell(ai.it.IndexCell().shapes[0], c.shapes[0]) {
        return true
        }
        }
    
        return false
    }

    // containsCenterMatches reports if the clippedShapes containsCenter boolean corresponds
    // to the crossing target type given. (This is to work around C++ allowing false == 0,
    // true == 1 type implicit conversions and comparisons)
    fn containsCenterMatches(a: *clippedShape, target: crossingTarget) -> bool {
        return ( ! a.containsCenter & & target == crossingTargetDontCross) | |
        (a.containsCenter & & target == crossingTargetCross)
    }

    // hasCrossingRelation reports whether given two iterators positioned such that
    // ai.cellID().ContainsCellID(bi.cellID()), there is a crossing relationship
    // anywhere within ai.cellID(). Specifically, this method returns true if there
    // is an edge crossing, a wedge crossing, or a point P that matches both relations
    // crossing targets. This fntion advances both iterators past ai.cellID.
    fn hasCrossingRelation(&mut self, ai: &rangeIterator, bi: &rangeIterator) -> bool {
        aClipped = ai.it.IndexCell().shapes[0]
        if aClipped.numEdges() != 0 {
        // The current cell of A has at least one edge, so check for crossings.
        if self.hasCrossing(ai, bi) {
        return true
        }
        ai.next()
        return false
        }

        if containsCenterMatches(aClipped, self .aCrossingTarget) {
            // The crossing target for A is not satisfied, so we skip over these cells of B.
            bi.seekBeyond(ai)
            ai.next()
            return false
        }

        // All points within ai.cellID() satisfy the crossing target for A, so it's
        // worth iterating through the cells of B to see whether any cell
        // centers also satisfy the crossing target for B.
        for bi.cellID() < = ai.rangeMax {
        bClipped = bi.it.IndexCell().shapes[0]
        if containsCenterMatches(bClipped, self .bCrossingTarget) {
        return true
        }
        bi.next()
        }
        ai.next()
        return false
    }

    // hasCrossingRelation checks all edges of loop A for intersection against all edges
    // of loop B and reports if there are any that satisfy the given relation. If there
    // is any shared vertex, the wedges centered at this vertex are sent to the given
    // relation to be tested.
    //
    // If the two loop boundaries cross, this method is guaranteed to return
    // true. It also returns true in certain cases if the loop relationship is
    // equivalent to crossing. For example, if the relation is Contains and a
    // point P is found such that B contains P but A does not contain P, this
    // method will return true to indicate that the result is the same as though
    // a pair of crossing edges were found (since Contains returns false in
    // both cases).
    //
    // See Contains, Intersects and CompareBoundary for the three uses of this fntion.
    fn hasCrossingRelation(a: &Loop, b: &Loop, relation: loopRelation) -> bool {
        // We look for CellID ranges where the indexes of A and B overlap, and
        // then test those edges for crossings.
        ai = newRangeIterator(a.index)
        bi = newRangeIterator(b.index)

        ab = newLoopCrosser(a, b, relation, false) // Tests edges of A against B
        ba = newLoopCrosser(b, a, relation, true)  // Tests edges of B against A

        for ! ai.done() | | ! bi.done() {
        if ai.rangeMax < bi.rangeMin {
        // The A and B cells don't overlap, and A precedes B.
        ai.seekTo(bi)
        } else if bi.rangeMax < ai.rangeMin {
        // The A and B cells don't overlap, and B precedes A.
        bi.seekTo(ai)
        } else {
        // One cell contains the other. Determine which cell is larger.
        abRelation = int64(ai.it.CellID().lsb() - bi.it.CellID().lsb())
        if abRelation > 0 {
        // A's index cell is larger.
        if ab.hasCrossingRelation(ai, bi) {
        return true
        }
        } else if abRelation < 0 {
        // B's index cell is larger.
        if ba.hasCrossingRelation(bi, ai) {
        return true
        }
        } else {
        // The A and B cells are the same. Since the two cells
        // have the same center point P, check whether P satisfies
        // the crossing targets.
        aClipped = ai.it.IndexCell().shapes[0]
        bClipped = bi.it.IndexCell().shapes[0]
        if containsCenterMatches(aClipped, ab.aCrossingTarget) & &
        containsCenterMatches(bClipped, ab.bCrossingTarget) {
        return true
        }
        // Otherwise test all the edge crossings directly.
        if aClipped.numEdges() > 0 & & bClipped.numEdges() > 0 & & ab.cellCrossesCell(aClipped, bClipped) {
        return true
        }
        ai.next()
        bi.next()
        }
        }
        }
        return false
    }
}
// containsRelation implements loopRelation for a contains operation. If
// A.ContainsPoint(P) == false && B.ContainsPoint(P) == true, it is equivalent
// to having an edge crossing (i.e., Contains returns false).
struct containsRelation {
    foundSharedVertex: bool
}
impl containsRelation {
    fn aCrossingTarget( &mut self ) -> crossingTarget { return crossingTargetDontCross }
    fn  bCrossingTarget( &mut self ) -> crossingTarget { return crossingTargetCross }
    fn  wedgesCross( &mut self , a0: &Point, ab1: &Point, a2: &Point, b0: &Point, b2: &Point) -> bool {
        c.foundSharedVertex = true;
        return !WedgeContains(a0, ab1, a2, b0, b2)
    }
}
// intersectsRelation implements loopRelation for an intersects operation. Given
// two loops, A and B, if A.ContainsPoint(P) == true && B.ContainsPoint(P) == true,
// it is equivalent to having an edge crossing (i.e., Intersects returns true).
struct intersectsRelation
{
    foundSharedVertex: bool
}
impl intersectsRelation {
    fn aCrossingTarget(&mut self) -> crossingTarget { return crossingTargetCross }
    fn bCrossingTarget(&mut self) -> crossingTarget { return crossingTargetCross }
    fn wedgesCross(&mut self, a0: &Point, ab1: &Point, a2: &Point, b0: &Point, b2: &Point) -> bool {
        i.foundSharedVertex = true;
        return WedgeIntersects(a0, ab1, a2, b0, b2)
    }
}
// compareBoundaryRelation implements loopRelation for comparing boundaries.
//
// The compare boundary relation does not have a useful early-exit condition,
// so we return crossingTargetDontCare for both crossing targets.
//
// Aside: A possible early exit condition could be based on the following.
//
//	If A contains a point of both B and ~B, then A intersects Boundary(B).
//	If ~A contains a point of both B and ~B, then ~A intersects Boundary(B).
//	So if the intersections of {A, ~A} with {B, ~B} are all non-empty,
//	the return value is 0, i.e., Boundary(A) intersects Boundary(B).
//
// Unfortunately it isn't worth detecting this situation because by the
// time we have seen a point in all four intersection regions, we are also
// guaranteed to have seen at least one pair of crossing edges.
struct compareBoundaryRelation {
    reverse:           bool // True if the other loop should be reversed.
    foundSharedVertex: bool // True if any wedge was processed.
    containsEdge:      bool // True if any edge of the other loop is contained by this loop.
    excludesEdge:      bool // True if any edge of the other loop is excluded by this loop.
}
impl compareBoundaryRelation {
    fn newCompareBoundaryRelation(reverse: bool) -> compareBoundaryRelation {
        return & compareBoundaryRelation{reverse: reverse}
    }

    fn a_crossing_target(&self) -> CrossingTarget { 
        CrossingTarget::DontCare 
    }
    
    fn b_crossing_target(&self) -> CrossingTarget { 
        CrossingTarget::DontCare 
    }
    
    fn wedges_cross(&mut self, a0: &Point, ab1: &Point, a2: &Point, b0: &Point, b2: &Point) -> bool {
        // Because we don't care about the interior of the other, only its boundary,
        // it is sufficient to check whether this one contains the semiwedge (ab1, b2).
        self.foundSharedVertex = true;
        if wedge_contains_semiwedge(a0, ab1, a2, b2, self.reverse) {
            self.containsEdge = true;
        } else {
            self.excludesEdge = true;
        }
        self.containsEdge && self.excludesEdge
    }
}
/// wedge_contains_semiwedge reports whether the wedge (a0, ab1, a2) contains the
/// "semiwedge" defined as any non-empty open set of rays immediately CCW from
/// the edge (ab1, b2). If reverse is true, then substitute clockwise for CCW;
/// this simulates what would happen if the direction of the other loop was reversed.
pub fn wedge_contains_semiwedge(a0: &Point, ab1: &Point, a2: &Point, b2: &Point, reverse: bool) -> bool {
    if b2 == a0 || b2 == a2 {
        // We have a shared or reversed edge.
        return (b2 == a0) == reverse;
    }
    ordered_ccw(a0, a2, b2, ab1)
}

// TODO(roberts): Differences from the C++ version:
// DistanceToPoint
// DistanceToBoundary
// Project
// ProjectToBoundary
// BoundaryApproxEqual
// BoundaryNear
/// ReferencePoint represents a reference point for a shape.
#[derive(Debug, Clone)]
pub struct ReferencePoint {
    /// The reference point
    pub point: Point,
    /// Whether the point is contained by the shape
    pub contained: bool,
}

/// Cap represents a spherical cap, i.e., a portion of a sphere cut off by a plane.
#[derive(Debug, Clone)]
pub struct Cap {
    /// The center of the cap
    pub center: Point,
    /// The height of the cap
    pub height: f64,
}

/// ShapeIndex is a spatial index for efficient lookup of shapes.
#[derive(Debug, Clone)]
pub struct ShapeIndex {
    // TODO: Implement this properly
    shapes: Vec<()>,
}

impl ShapeIndex {
    /// Creates a new ShapeIndex
    pub fn new() -> Self {
        ShapeIndex { shapes: Vec::new() }
    }
}

/// origin_point returns the point at the origin of the sphere.
pub fn origin_point() -> Point {
    Point(Vector { x: 0.0, y: 0.0, z: 0.0 })
}

/// origin_reference_point returns a ReferencePoint for the origin.
pub fn origin_reference_point(contains_origin: bool) -> ReferencePoint {
    ReferencePoint {
        point: origin_point(),
        contained: contains_origin,
    }
}
impl Rect {
    /// Creates an empty rectangle
    pub fn empty() -> Self {
        // Implementation depends on your Rect definition
        Rect::from_lat_lng(
            r1::Interval::empty(),
            s1::Interval::empty()
        )
    }
    
    /// Creates a full rectangle covering the entire sphere
    pub fn full() -> Self {
        // Implementation depends on your Rect definition
        Rect::from_lat_lng(
            r1::Interval::new(-PI/2.0, PI/2.0),
            s1::Interval::full()
        )
    }
    
    /// Creates a rectangle from latitude and longitude intervals
    pub fn from_lat_lng(lat: r1::Interval, lng: s1::Interval) -> Self {
        Rect { lat, lng }
    }
    
    /// Checks if the rectangle contains the given point
    pub fn contains_point(&self, p: &Point) -> bool {
        // Convert point to lat/lng
        let lat = p.0.z.asin();
        let lng = p.0.y.atan2(p.0.x);
        
        self.lat.contains(lat) && self.lng.contains(lng)
    }
}
impl s1::Interval {
    /// Creates a new interval with the given bounds
    pub fn new(lo: f64, hi: f64) -> Self {
        s1::Interval { lo, hi }
    }
    
    /// Creates an empty interval
    pub fn empty() -> Self {
        s1::Interval { lo: 1.0, hi: 0.0 }
    }
    
    /// Creates a full interval covering the entire range
    pub fn full() -> Self {
        s1::Interval { lo: -PI, hi: PI }
    }
    
    /// Checks if the interval contains the given value
    pub fn contains(&self, v: f64) -> bool {
        if self.lo <= self.hi {
            self.lo <= v && v <= self.hi
        } else {
            // Wrapping interval
            self.lo <= v || v <= self.hi
        }
    }
}

impl r1::Interval {
    /// Creates a new interval with the given bounds
    pub fn new(lo: f64, hi: f64) -> Self {
        r1::Interval { lo, hi }
    }
    
    /// Creates an empty interval
    pub fn empty() -> Self {
        r1::Interval { lo: 1.0, hi: 0.0 }
    }
    
    /// Checks if the interval contains the given value
    pub fn contains(&self, v: f64) -> bool {
        self.lo <= v && v <= self.hi
    }
}
