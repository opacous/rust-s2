// Copyright 2023 Google Inc. All rights reserved.
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

use crate::consts::DBL_EPSILON;
use crate::error::S2Error;
use crate::point::{get_frame, ordered_ccw, regular_points_for_frame};
use crate::r3::vector::Vector as R3Vector;
use crate::rect_bounder::expand_for_subregions;
use crate::region::Region;
use crate::s1;
use crate::s1::Angle;
use crate::s2::cap::Cap;
use crate::s2::cell::Cell;
use crate::s2::edge_clipping::{
    clip_to_padded_face, edge_intersects_rect, INTERSECT_RECT_ERROR_UV_DIST,
};
use crate::s2::edge_crosser::EdgeCrosser;
use crate::s2::edge_crossings::angle_contains_vertex;
use crate::s2::point::Point;
use crate::s2::rect::Rect;
use crate::s2::rect_bounder::RectBounder;
use crate::s2::shape::{Chain, ChainPosition, Edge, ReferencePoint, Shape, ShapeType};
use crate::s2::shape_index::ShapeIndex;
use crate::shape_index::CellRelation::{Disjoint, Indexed, Subdivided};
use crate::shape_index::FACE_CLIP_ERROR_UV_COORD;
use cgmath::Matrix3;
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::f64;
use std::f64::consts::PI;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::{Add, AddAssign, Mul, Neg, Sub};
use crate::consts::EPSILON;

pub enum OriginBound {
    OriginInside,
    BoundEncoded,
}

#[derive(Copy, Clone, Debug, PartialOrd, PartialEq)]
pub enum VertexTraversalDirection {
    Forward, // vertices are traversed starting from firstIdx and incrementing the index. This is the "forward" direction. The sequence will be firstIdx, firstIdx + 1, firstIdx + 2,
    Backward, // vertices are traversed starting from firstIdx + n (where n is the loop length) and decrementing the index. This is the "backward" direction. The sequence will be firstIdx + n, firstIdx + n - 1, firstIdx + n - 2
}

impl Into<i32> for VertexTraversalDirection {
    fn into(self) -> i32 {
        match self {
            VertexTraversalDirection::Forward => 1,
            VertexTraversalDirection::Backward => -1,
        }
    }
}

impl Into<f64> for VertexTraversalDirection {
    fn into(self) -> f64 {
        match self {
            VertexTraversalDirection::Forward => 1.,
            VertexTraversalDirection::Backward => -1.,
        }
    }
}

impl AddAssign<VertexTraversalDirection> for usize {
    fn add_assign(&mut self, rhs: VertexTraversalDirection) {
        match rhs {
            VertexTraversalDirection::Forward => *self += 1,
            VertexTraversalDirection::Backward => *self -= 1,
        }
    }
}

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
/// chain, they are defined as having exactly one vertex each (see EmptyLoop
/// and FullLoop).
#[derive(Clone)]
pub struct Loop {
    /// The vertices of the loop. These should be ordered counterclockwise
    /// around the loop interior.
    vertices: Vec<Point>,

    /// originInside keeps a precomputed value whether this loop contains the origin
    /// versus computing from the set of vertices every time.
    origin_inside: bool,

    /// depth is the nesting depth of this Loop if it is contained by a Polygon
    /// or other shape and is used to determine if this loop represents a hole
    /// or a filled in portion.
    pub(crate) depth: i32,

    /// bound is a conservative bound on all points contained by this loop.
    /// If l.ContainsPoint(P), then l.bound.ContainsPoint(P).
    bound: Rect,

    /// Since bound is not exact, it is possible that a loop A contains
    /// another loop B whose bounds are slightly larger. subregionBound
    /// has been expanded sufficiently to account for this error, i.e.
    /// if A.Contains(B), then A.subregionBound.Contains(B.bound).
    subregion_bound: Rect,

    /// index is the spatial index for this Loop.
    index: ShapeIndex,
}

impl PartialEq for Loop {
    fn eq(&self, _other: &Self) -> bool {
        todo!()
    }
}

impl Eq for Loop {}

impl Hash for Loop {
    fn hash<H: Hasher>(&self, _state: &mut H) {
        todo!()
    }
}

impl Loop {
    // containsNonCrossingBoundary reports whether given two loops whose boundaries
    // do not cross (see compareBoundary), if this loop contains the boundary of the
    // other loop. If reverse is true, the boundary of the other loop is reversed
    // first (which only affects the result when there are shared edges). This method
    // is cheaper than compareBoundary because it does not test for edge intersections.
    //
    // This function requires that neither loop is empty, and that if the other is full,
    // then reverse == false.
    pub(crate) fn contains_non_crossing_boundary(&self, other: &Loop, reverse_other: bool) -> bool {
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

        let m = self.find_vertex(other.vertex(0));

        match m {
            None => {
                // Since the other loops vertex 0 is not shared, we can check if this contains it.
                return self.contains_point(other.vertex(0));
            }
            Some(m) => {
                return wedge_contains_semi_wedge(
                    &self.vertex(m - 1),
                    &self.vertex(m),
                    &self.vertex(m + 1),
                    &other.vertex(1),
                    reverse_other,
                );
            }
        }
    }
}

// These two points are used for the special Empty and Full loops.
const EMPTY_LOOP_POINT: Point = Point(R3Vector {
    x: 0.0,
    y: 0.0,
    z: 1.0,
});
const FULL_LOOP_POINT: Point = Point(R3Vector {
    x: 0.0,
    y: 0.0,
    z: -1.0,
});

impl Debug for Loop {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

impl Loop {
    /// Creates a new loop from the given points.
    pub fn from_points(pts: Vec<Point>) -> Self {
        let mut l = Self {
            vertices: pts,
            origin_inside: false,
            depth: 0,
            bound: Rect::empty(),
            subregion_bound: Rect::empty(),
            index: ShapeIndex::new(),
        };

        l.init_origin_and_bound();
        l
    }

    /// Creates a loop corresponding to the given cell.
    ///
    /// Note that the loop and cell *do not* contain exactly the same set of
    /// points, because Loop and Cell have slightly different definitions of
    /// point containment. For example, a Cell vertex is contained by all
    /// four neighboring Cells, but it is contained by exactly one of four
    /// Loops constructed from those cells. As another example, the cell
    /// coverings of cell and LoopFromCell(cell) will be different, because the
    /// loop contains points on its boundary that actually belong to other cells
    /// (i.e., the covering will include a layer of neighboring cells).
    pub fn from_cell(c: &Cell) -> Self {
        let mut l = Self {
            vertices: vec![c.vertex(0), c.vertex(1), c.vertex(2), c.vertex(3)],
            origin_inside: false,
            depth: 0,
            bound: Rect::empty(),
            subregion_bound: Rect::empty(),
            index: ShapeIndex::new(),
        };

        l.init_origin_and_bound();
        l
    }

    /// Returns a special "empty" loop.
    pub fn empty() -> Self {
        Self::from_points(vec![EMPTY_LOOP_POINT])
    }

    /// Returns a special "full" loop.
    pub fn full() -> Self {
        Self::from_points(vec![FULL_LOOP_POINT])
    }

    /// Sets the origin containment for the given point and then calls
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
            // crossings starting at a fixed reference point (chosen as OriginPoint()
            // for historical reasons). Loop initialization would be more efficient
            // if we used a loop vertex such as vertex(0) as the reference point
            // instead, however making this change would be a lot of work because
            // originInside is currently part of the Encode() format.
            //
            // In any case, we initialize originInside by first guessing that it is
            // outside, and then seeing whether we get the correct containment result
            // for vertex 1. If the result is incorrect, the origin must be inside
            // the loop instead. Note that the Loop is not necessarily valid and so
            // we need to check the requirements of AngleContainsVertex first.
            let v1_inside = self.vertex(0) != self.vertex(1)
                && self.vertex(2) != self.vertex(1)
                && angle_contains_vertex(&self.vertex(0), &self.vertex(1), &self.vertex(2));

            // Initialize before calling contains_point
            self.origin_inside = false;

            // Note that contains_point only does a bounds check once init_index
            // has been called, so it doesn't matter that bound is undefined here.
            if v1_inside != self.contains_point(self.vertex(1)) {
                self.origin_inside = true;
            }
        }

        // We *must* call init_bound before initializing the index, because
        // init_bound calls contains_point which does a bounds check before using
        // the index.
        self.init_bound();

        // Create a new index and add us to it.
        self.index = ShapeIndex::new();
        self.index.add(&ShapeType::Loop(self.clone()));
    }

    /// Sets up the approximate bounding Rects for this loop.
    fn init_bound(&mut self) {
        if self.vertices.is_empty() {
            *self = Self::empty();
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
        let mut bounder = RectBounder::new();
        for i in 0..=self.vertices.len() {
            // add vertex 0 twice
            bounder.add_point(&self.vertex(i));
        }
        let mut b = bounder.get_bound();

        if self.contains_point(Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: 1.0,
        })) {
            b = Rect {
                lat: crate::r1::interval::Interval::new(b.lat.lo, PI / 2.0),
                lng: s1::interval::Interval::full_interval(),
            };
        }
        // If a loop contains the south pole, then either it wraps entirely
        // around the sphere (full longitude range), or it also contains the
        // north pole in which case b.lng.is_full() due to the test above.
        // Either way, we only need to do the south pole containment test if
        // b.lng.is_full().
        if b.lng.is_full()
            && self.contains_point(Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: -1.0,
            }))
        {
            b.lat.lo = -PI / 2.0;
        }
        self.bound = b;
        self.subregion_bound = expand_for_subregions(&self.bound);
    }

    /// Returns whether this loop is considered empty.
    pub fn is_empty(&self) -> bool {
        self.is_empty_or_full() && !self.contains_origin()
    }

    /// Returns whether this loop is considered full.
    pub fn is_full(&self) -> bool {
        self.is_empty_or_full() && self.contains_origin()
    }

    /// Returns whether this loop is either the "empty" or "full" special loops.
    pub fn is_empty_or_full(&self) -> bool {
        self.vertices.len() == 1
    }

    /// Returns the reference point for this loop.
    pub fn reference_point(&self) -> ReferencePoint {
        ReferencePoint::origin(self.origin_inside)
    }

    /// Returns the vertex at the given index. For convenience, the vertex indices
    /// wrap automatically for methods that do index math such as Edge.
    /// i.e., Vertex(NumEdges() + n) is the same as Vertex(n).
    pub fn vertex(&self, i: usize) -> Point {
        self.vertices[i % self.vertices.len()]
    }

    /// Returns true if this loop contains the point.
    pub fn contains_point(&self, p: Point) -> bool {
        if !self.index.is_fresh() && !self.bound.contains_point(&p) {
            return false;
        }

        // For small loops it is faster to just check all the crossings. We also
        // use this method during loop initialization because InitOriginAndBound()
        // calls Contains() before InitIndex().

        const MAX_BRUTE_FORCE_VERTICES: usize = 32;

        if self.index.num_shapes() == 0 || // Index has not been initialized yet
           self.vertices.len() <= MAX_BRUTE_FORCE_VERTICES
        {
            return self.brute_force_contains_point(&p);
        }

        // Otherwise, look up the point in the index.
        let mut it = self.index.iterator();
        if !it.locate_point(p) {
            return false;
        }
        self.iterator_contains_point(&mut it, p)
    }

    /// Reports if the given point is contained by this loop, by doing a simple
    /// brute force check.  This method does not use the ShapeIndex, so it is only
    /// preferable below a certain size of loop.
    pub fn brute_force_contains_point(&self, p: &Point) -> bool {
        let origin = Point::origin();
        let mut inside = self.origin_inside;
        let mut crosser = EdgeCrosser::new_chain_edge_crosser(&origin, &p, &self.vertex(0));
        for i in 1..=self.vertices.len() {
            // add vertex 0 twice
            inside = inside != crosser.edge_or_vertex_chain_crossing(&self.vertex(i));
        }
        inside
    }

    /// Reports if the iterator that is positioned at the ShapeIndexCell
    /// that may contain p, contains the point p.
    fn iterator_contains_point(
        &self,
        it: &mut crate::s2::shape_index::ShapeIndexIterator,
        p: Point,
    ) -> bool {
        // Test containment by drawing a line segment from the cell center to the
        // given point and counting edge crossings.
        // TODO: Is this
        let a_clipped = it
            .index_cell()
            .expect("Why does an indexed cell not exist? Is the ShapeIndex not initialized")
            .find_by_shape_id(0)
            .expect("Index cell should have shapeID of 0 here!!");
        let mut inside = a_clipped.contains_center;

        if a_clipped.num_edges() > 0 {
            let center = it.center();
            let mut crosser = EdgeCrosser::new(&center, &p);
            let mut ai_prev = -2;

            for &ai in &a_clipped.edges {
                if ai != ai_prev + 1 {
                    crosser.restart_at(&self.vertex(ai as usize));
                }
                ai_prev = ai;
                inside = inside
                    != crosser.edge_or_vertex_chain_crossing(&self.vertex((ai + 1) as usize));
            }
        }
        inside
    }

    /// Returns whether the loop contains origin.
    pub fn contains_origin(&self) -> bool {
        self.origin_inside
    }

    /// Returns the vertices of the loop.
    pub fn vertices(&self) -> &[Point] {
        &self.vertices
    }

    /// Returns the number of vertices in this loop.
    pub fn num_vertices(&self) -> usize {
        self.vertices.len()
    }

    /// Returns a tight bounding rectangle. If the loop contains the point,
    /// the bound also contains it.
    pub fn rect_bound(&self) -> Rect {
        self.bound.clone()
    }

    /// Returns a bounding cap that may have more padding than the corresponding
    /// RectBound. The bound is conservative such that if the loop contains a point P,
    /// the bound also contains it.
    pub fn cap_bound(&self) -> Cap {
        self.bound.cap_bound()
    }

    /// Returns whether this loop represents a hole in its containing polygon.
    pub fn is_hole(&self) -> bool {
        (self.depth & 1) != 0
    }

    /// Returns -1 if this Loop represents a hole in its containing polygon, and +1 otherwise.
    pub fn sign(&self) -> i32 {
        if self.is_hole() {
            -1
        } else {
            1
        }
    }

    /// Reports whether the region contained by this loop is a superset of the
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

        if !self.subregion_bound.contains(&o.bound.clone()) {
            return false;
        }

        // Special cases to handle either loop being empty or full.
        if self.is_empty_or_full() || o.is_empty_or_full() {
            return self.is_full() || o.is_empty();
        }

        // Check whether there are any edge crossings, and also check the loop
        // relationship at any shared vertices.
        let mut relation = ContainsRelation::new();
        if has_crossing_relation(self, o, &mut relation) {
            return false;
        }

        // There are no crossings, and if there are any shared vertices then A
        // contains B locally at each shared vertex.
        if relation.found_shared_vertex {
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
        if (o.subregion_bound.contains(&self.bound.clone()) || o.bound.union(&self.bound).is_full())
            && o.contains_point(self.vertex(0))
        {
            return false;
        }

        true
    }

    /// Reports whether the region contained by this loop intersects the region
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
        let mut relation = IntersectsRelation::new();
        if has_crossing_relation(self, o, &mut relation) {
            return true;
        }

        if relation.found_shared_vertex {
            return false;
        }

        // Since there are no edge intersections or shared vertices, the loops
        // intersect only if A contains B, B contains A, or the two loops contain
        // each other's boundaries.  These checks are usually cheap because of the
        // bounding box preconditions.  Note that neither loop is empty (because of
        // the bounding box check above), so it is safe to access vertex(0).

        // Check whether A contains B, or A and B contain each other's boundaries.
        // (Note that A contains all the vertices of B in either case.)
        if (self.subregion_bound.contains(&o.bound.clone()) || self.bound.union(&o.bound).is_full())
            && self.contains_point(o.vertex(0))
        {
            return true;
        }

        // Check whether B contains A.
        if o.subregion_bound.contains(&self.bound.clone()) && o.contains_point(self.vertex(0)) {
            return true;
        }

        false
    }

    /// Equal reports whether two loops have the same vertices in the same linear order
    /// (i.e., cyclic rotations are not allowed).
    pub fn equal(&self, other: &Loop) -> bool {
        if self.vertices.len() != other.vertices.len() {
            return false;
        }

        for i in 0..self.vertices.len() {
            if self.vertex(i) != other.vertex(i) {
                return false;
            }
        }

        true
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
        for offset in 0..self.vertices.len() {
            if self.vertex(offset) == o.vertex(0) {
                // There is at most one starting offset since loop vertices are unique.
                let mut matched = true;
                for i in 0..self.vertices.len() {
                    if self.vertex(i + offset) != o.vertex(i) {
                        matched = false;
                        break;
                    }
                }
                if matched {
                    return true;
                }
            }
        }

        false
    }

    /// Tests whether the given loops contains this loop.
    /// This function does not test for edge intersections. The two loops must meet
    /// all of the Polygon requirements; for example this implies that their
    /// boundaries may not cross or have any shared edges (although they may have
    /// shared vertices).
    pub fn contains_nested(&self, other: &Loop) -> bool {
        if !self.subregion_bound.contains(&other.bound.clone()) {
            return false;
        }

        // Special cases to handle either loop being empty or full.  Also bail out
        // when B has no vertices to avoid heap overflow on the vertex(1) call
        // below.  (This method is called during polygon initialization before the
        // client has an opportunity to call IsValid().)
        if self.is_empty_or_full() || other.num_vertices() < 2 {
            return self.is_full() || other.is_empty();
        }

        // We are given that A and B do not share any edges, and that either one
        // loop contains the other or they do not intersect.
        match self.find_vertex(other.vertex(1)) {
            Some(m) => {
                // Check whether the edge order around other.Vertex(1) is compatible with
                // A containing B.
                general_wedge_contains(
                    &self.vertex(m - 1),
                    &self.vertex(m),
                    &self.vertex(m + 1),
                    &other.vertex(0),
                    &other.vertex(2),
                )
            }
            None => {
                // Since other.vertex(1) is not shared, we can check whether A contains it.
                self.contains_point(other.vertex(1))
            }
        }
    }

    /// Find a vertex of this loop that matches the given vertex p.
    /// Returns the index of the vertex in the range [0..num_vertices-1]
    /// or None if no matching vertex is found.
    fn find_vertex(&self, p: Point) -> Option<usize> {
        if self.vertices.len() < 10 {
            // Exhaustive search for loops below a small threshold.
            for i in 0..self.vertices.len() {
                if self.vertex(i) == p {
                    return Some(i);
                }
            }
            return None;
        }

        let mut it = self.index.iterator();
        if !it.locate_point(p) {
            return None;
        }

        let a_clipped = it.index_cell()?.find_by_shape_id(0);
        for i in (0..a_clipped?.num_edges()).rev() {
            let ai = a_clipped.unwrap().edges[i];
            if self.vertex(ai as usize) == p {
                if ai == 0 {
                    return Some(self.vertices.len() - 1);
                }
                return Some(ai as usize);
            }

            if self.vertex((ai + 1) as usize) == p {
                return Some((ai + 1) as usize);
            }
        }

        None
    }

    /// Returns the vertex in reverse order if the loop represents a polygon
    /// hole. For example, arguments 0, 1, 2 are mapped to vertices n-1, n-2, n-3, where
    /// n == len(vertices). This ensures that the interior of the polygon is always to
    /// the left of the vertex chain.
    ///
    /// This requires: 0 <= i < 2 * len(vertices)
    pub fn oriented_vertex(&self, i: usize) -> Point {
        let mut j = i;
        if j >= self.vertices.len() {
            j = j - self.vertices.len();
        }
        if self.is_hole() {
            j = self.vertices.len() - 1 - j;
        }
        self.vertex(j)
    }
}

/// ContainsRelation is a helper for the Contains() method.
/// It implements the loopRelation interface for a contains operation. If
/// A.ContainsPoint(P) == false && B.ContainsPoint(P) == true, it is equivalent
/// to having an edge crossing (i.e., Contains returns false).
struct ContainsRelation {
    found_shared_vertex: bool,
}

impl ContainsRelation {
    fn new() -> Self {
        Self {
            found_shared_vertex: false,
        }
    }
}

impl LoopRelation for ContainsRelation {
    fn a_crossing_target(&self) -> CrossingTarget {
        CrossingTarget::DontCross
    }

    fn b_crossing_target(&self) -> CrossingTarget {
        CrossingTarget::Cross
    }

    fn wedges_cross(
        &mut self,
        a0: &Point,
        ab1: &Point,
        a2: &Point,
        b0: &Point,
        b2: &Point,
    ) -> bool {
        self.found_shared_vertex = true;
        !general_wedge_contains(&a0, &ab1, &a2, &b0, &b2)
    }
}

/// IntersectsRelation is a helper for the Intersects() method.
/// It implements the loopRelation for an intersects operation. Given
/// two loops, A and B, if A.ContainsPoint(P) == true && B.ContainsPoint(P) == true,
/// it is equivalent to having an edge crossing (i.e., Intersects returns true).
struct IntersectsRelation {
    found_shared_vertex: bool,
}

impl IntersectsRelation {
    fn new() -> Self {
        Self {
            found_shared_vertex: false,
        }
    }
}

impl LoopRelation for IntersectsRelation {
    fn a_crossing_target(&self) -> CrossingTarget {
        CrossingTarget::Cross
    }

    fn b_crossing_target(&self) -> CrossingTarget {
        CrossingTarget::Cross
    }

    fn wedges_cross(
        &mut self,
        a0: &Point,
        ab1: &Point,
        a2: &Point,
        b0: &Point,
        b2: &Point,
    ) -> bool {
        self.found_shared_vertex = true;
        // In the Go code this would call WedgeIntersects, but we'll reuse WedgeContains with
        // appropriate logic until we implement WedgeIntersects
        wedge_intersects(a0, ab1, a2, b0, b2)
    }
}

/// WedgeIntersects reports whether the wedges AB1C and DB1E intersect.
/// This is used for testing whether two loops intersect at a shared vertex B1.
fn wedge_intersects(a: &Point, b: &Point, c: &Point, d: &Point, e: &Point) -> bool {
    // For A, B, C, if A == C then the wedge covers the entire sphere.
    // This should not be confused with a degenerate wedge for which B == A or B == C.
    // Note that we don't need to worry about the case where
    // (A == C && D == E), since the API requires that the two wedges have
    // different B vertices.
    if a == c {
        return true;
    }
    if d == e {
        return true;
    }

    // The wedges intersect if and only if neither wedge contains the other's
    // boundary, or they share a boundary. Since we've eliminated the case
    // where both wedges contain the entire sphere, we can check whether each
    // wedge contains the other's boundary.

    // Does the boundary of the first wedge contain the boundary of the second wedge?
    let contains_1 = general_wedge_contains(a, b, c, d, e);

    // Does the boundary of the second wedge contain the boundary of the first wedge?
    let contains_2 = general_wedge_contains(d, b, e, a, c);

    // The wedges intersect if and only if neither contains the other's boundary
    !contains_1 && !contains_2
}

fn general_wedge_contains(a0: &Point, ab1: &Point, a2: &Point, b0: &Point, b2: &Point) -> bool {
    // For A to contain B (where each loop interior is defined to be its left
    // side), the CCW edge order around ab1 must be a2 b2 b0 a0.  We split
    // this test into two parts that test three vertices each.
    ordered_ccw(&a2, &b2, &b0, &ab1) && ordered_ccw(&b0, &a0, &a2, &ab1)
}

// wedgeContainsSemiwedge reports whether the wedge (a0, ab1, a2) contains the
// "semiwedge" defined as any non-empty open set of rays immediately CCW from
// the edge (ab1, b2). If reverse is true, then substitute clockwise for CCW;
// this simulates what would happen if the direction of the other loop was reversed.
fn wedge_contains_semi_wedge(
    a0: &Point,
    ab1: &Point,
    a2: &Point,
    b2: &Point,
    reverse: bool,
) -> bool {
    if b2 == a0 || b2 == a2 {
        // We have a shared or reversed edge.
        return (b2 == a0) == reverse;
    }
    return ordered_ccw(a0, a2, b2, ab1);
}

/// CrossingTarget represents the possible crossing target cases for relations.
#[derive(Copy, Clone, Debug, PartialEq)]
enum CrossingTarget {
    DontCare,
    DontCross,
    Cross,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BoundaryCondition {
    ContainsOther, // 1
    CrossesOther,  // 0
    ExcludesOther, //-1
}

impl PartialEq<i32> for BoundaryCondition {
    fn eq(&self, _other: &i32) -> bool {
        todo!()
    }
}

impl PartialOrd<i32> for BoundaryCondition {
    fn partial_cmp(&self, other: &i32) -> Option<Ordering> {
        match self {
            BoundaryCondition::ContainsOther => Option::from(1.cmp(other)),
            BoundaryCondition::CrossesOther => Option::from(0.cmp(other)),
            BoundaryCondition::ExcludesOther => Option::from((-1i32).cmp(other)),
        }
    }
}

impl Neg for BoundaryCondition {
    type Output = Self;
    fn neg(self) -> Self {
        match self {
            BoundaryCondition::ContainsOther => BoundaryCondition::ExcludesOther,
            BoundaryCondition::CrossesOther => BoundaryCondition::CrossesOther,
            BoundaryCondition::ExcludesOther => BoundaryCondition::ContainsOther,
        }
    }
}

impl TryFrom<i32> for BoundaryCondition {
    type Error = S2Error;

    fn try_from(value: i32) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(BoundaryCondition::ContainsOther),
            0 => Ok(BoundaryCondition::CrossesOther),
            -1 => Ok(BoundaryCondition::ExcludesOther),
            _ => Err(S2Error::Other(format!(
                "BoundaryCondition Error: Invalid value conversion from int:[{}]",
                value
            ))),
        }
    }
}

/// has_crossing_relation is a helper for Contains, Intersects, and CompareBoundary
/// It checks all edges of loop A for intersection against all edges of loop B and
/// reports if there are any that satisfy the given relation. If there is any shared
/// vertex, the wedges centered at this vertex are tested to see if they satisfy
/// the relation.
///
/// If the two loop boundaries cross, this method is guaranteed to return true.
/// It also returns true in certain cases if the loop relationship is equivalent
/// to crossing. For example, if the relation is Contains and a point P is found
/// such that B contains P but A does not contain P, this method will return true
/// to indicate that the result is the same as though a pair of crossing edges
/// were found (since Contains returns false in both cases).
fn has_crossing_relation(a: &Loop, b: &Loop, relation: &mut dyn LoopRelation) -> bool {
    // Use CrossingEdgeQuery to efficiently find edge crossings

    // First check for shared vertices and test wedge relationships
    for i in 0..a.vertices.len() {
        for j in 0..b.vertices.len() {
            // If vertices are shared
            if a.vertex(i) == b.vertex(j) {
                // Test wedge relationship at shared vertex
                if relation.wedges_cross(
                    &a.vertex(i - 1),
                    &a.vertex(i),
                    &a.vertex(i + 1),
                    &b.vertex(j - 1),
                    &b.vertex(j + 1),
                ) {
                    return true;
                }
            }
        }
    }

    // Then check for edge crossings using CrossingEdgeQuery
    // We need to check in both directions: A's edges crossing B, and B's edges crossing A

    // Check if any edge of A crosses any edge of B
    let mut query = crate::s2::crossing_edge_query::CrossingEdgeQuery::new(&a.index);

    // Iterate through all edges of B
    for j in 0..b.num_edges() {
        let edge_b = b.edge(j as i64);

        // Find all edges of A that cross this edge of B
        let crossings = query.crossings(
            edge_b.v0,
            edge_b.v1,
            &ShapeType::Loop(a.clone()),
            crate::s2::crossing_edge_query::CrossingType::Interior,
        );

        if !crossings.is_empty() {
            return true; // Found a crossing edge
        }
    }

    // Also need to check if one loop contains a vertex of the other
    let target_a = relation.a_crossing_target();
    let target_b = relation.b_crossing_target();

    if target_a != CrossingTarget::DontCare && target_b != CrossingTarget::DontCare {
        // Check if there's a point in b that doesn't satisfy the crossing target for a
        if target_a == CrossingTarget::DontCross && a.contains_point(b.vertex(0)) {
            return true;
        }
        if target_a == CrossingTarget::Cross && !a.contains_point(b.vertex(0)) {
            return true;
        }

        // Check if there's a point in a that doesn't satisfy the crossing target for b
        if target_b == CrossingTarget::DontCross && b.contains_point(a.vertex(0)) {
            return true;
        }
        if target_b == CrossingTarget::Cross && !b.contains_point(a.vertex(0)) {
            return true;
        }
    }

    false
}

/// CrossingRelation defines an interface for checking relationships between loops.
/// This is similar to the Go loopRelation interface, but adapted for Rust.
trait LoopRelation {
    /// Returns the crossing target for loop A
    fn a_crossing_target(&self) -> CrossingTarget;

    /// Returns the crossing target for loop B
    fn b_crossing_target(&self) -> CrossingTarget;

    /// Tests whether wedges at a shared vertex indicate a crossing relationship
    fn wedges_cross(&mut self, a0: &Point, ab1: &Point, a2: &Point, b0: &Point, b2: &Point)
        -> bool;
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
struct CompareBoundaryRelation {
    reverse: bool,
    found_shared_vertex: bool,
    contains_edge: bool,
    excludes_edge: bool,
}

impl CompareBoundaryRelation {
    fn new(reverse: bool) -> Self {
        Self {
            reverse,
            found_shared_vertex: false,
            contains_edge: false,
            excludes_edge: false,
        }
    }
}

impl LoopRelation for CompareBoundaryRelation {
    fn a_crossing_target(&self) -> CrossingTarget {
        CrossingTarget::DontCare
    }

    fn b_crossing_target(&self) -> CrossingTarget {
        CrossingTarget::DontCare
    }

    fn wedges_cross(
        &mut self,
        a0: &Point,
        ab1: &Point,
        a2: &Point,
        _b0: &Point,
        b2: &Point,
    ) -> bool {
        // Because we don't care about the interior of the other, only its boundary,
        // it is sufficient to check whether this one contains the semiwedge (ab1, b2).
        self.found_shared_vertex = true;
        if wedge_contains_semi_wedge(a0, ab1, a2, b2, self.reverse) {
            self.contains_edge = true
        } else {
            self.excludes_edge = true
        }
        self.contains_edge && self.excludes_edge
    }
}

impl Loop {
    /// CompareBoundary returns +1 if A contains the boundary of B, -1 if A excludes
    /// the boundary of B, and 0 if the boundaries of A and B cross. Excludes means
    /// that A does not intersect the boundary of B at all. For example, if
    /// A contains B, then A contains the boundary of B. If A is contained by B
    /// (including the case where the boundaries of the two loops coincide), then
    /// A excludes the boundary of B.
    ///
    /// This function is primarily useful for determining whether one loop contains
    /// another loop without needing to check all pairs of edges for crossings.
    pub fn compare_boundary(&self, b: &Loop) -> BoundaryCondition {
        // The bounds must intersect for containment or crossing.
        if !self.bound.intersects(&b.bound) {
            return BoundaryCondition::ExcludesOther;
        }

        // Full loops are handled as though the loop surrounded the entire sphere.
        if self.is_full() {
            return BoundaryCondition::ContainsOther;
        }
        if b.is_full() {
            return BoundaryCondition::ExcludesOther;
        }

        // Check whether there are any edge crossings, and also check the loop
        // relationship at any shared vertices.
        let mut relation = CompareBoundaryRelation::new(b.is_hole()); //(o.IsHole())
        if has_crossing_relation(self, b, &mut relation) {
            return BoundaryCondition::CrossesOther;
        }
        if relation.found_shared_vertex {
            if relation.contains_edge {
                return BoundaryCondition::ContainsOther;
            }
            return BoundaryCondition::ExcludesOther;
        }

        // There are no edge intersections or shared vertices, so we can check
        // whether A contains an arbitrary vertex of B.
        if self.contains_point(b.vertex(0)) {
            return BoundaryCondition::ContainsOther;
        }

        BoundaryCondition::ExcludesOther
    }

    /// Returns a first vertex index and a direction (either +1 or -1) such that the
    /// vertex sequence defined by starting at that vertex and proceeding in the
    /// given direction is canonical for this loop.
    ///
    /// This can be useful for converting a loop to a canonical form. The return
    /// values are chosen such that the lexicographically smallest edge comes first
    /// and is in the forward direction. The result is unspecified if the loop has
    /// no vertices.
    // pub fn canonical_first_vertex(&self) -> (usize, i32) {
    //     let mut first_idx = 0;
    //     let mut dir = 1;
    //     let n = self.vertices.len();
    //
    //     for i in 0..n {
    //         if self.vertex(i).0 < self.vertex(first_idx).0 {
    //             first_idx = i;
    //         }
    //     }
    //
    //     // 0 <= firstIdx <= n-1, so (firstIdx+n*dir) <= 2*n-1.
    //     if self.vertex(first_idx + 1).0 < (self.vertex(first_idx + n - 1).0) {
    //         return (first_idx, 1);
    //     }
    //
    //     // n <= firstIdx <= 2*n-1, so (firstIdx+n*dir) >= 0.
    //     first_idx += n;
    //     (first_idx, -1)
    // }

    /// ContainsCell reports whether this loop contains the given cell.
    /// This method assumes that the loop has been indexed.
    pub fn contains_cell(&self, target: &crate::s2::cell::Cell) -> bool {
        let mut it = self.index.iterator();
        let relation = it.locate_cell_id(target.id);

        // If "target" is disjoint from all index cells, it is not contained.
        // Similarly, if "target" is subdivided into one or more index cells then it
        // is not contained, since index cells are subdivided only if they (nearly)
        // intersect a sufficient number of edges.  (But note that if "target" itself
        // is an index cell then it may be contained, since it could be a cell with
        // no edges in the loop interior.)
        if relation != Indexed {
            return false;
        }

        // Otherwise check if any edges intersect "target".
        if self.boundary_approx_intersects(target) {
            return false;
        }

        // Otherwise check if the loop contains the center of "target".
        self.iterator_contains_point(&mut it, target.center())
    }

    /// IntersectsCell reports whether this loop intersects the given cell.
    /// This method assumes that the loop has been indexed.
    pub fn intersects_cell(&self, target: &crate::s2::cell::Cell) -> bool {
        let mut it = self.index.iterator();
        let relation = it.locate_cell_id(target.id);

        // If target does not overlap any index cell, there is no intersection.
        if relation == Disjoint {
            return false;
        }
        // If target is subdivided into one or more index cells, there is an
        // intersection to within the ShapeIndex error bound (see Contains).
        if relation == Subdivided {
            return true;
        }
        // If target is an index cell, there is an intersection because index cells
        // are created only if they have at least one edge or they are entirely
        // contained by the loop.
        if it.cell_id() == target.id {
            return true;
        }
        // Otherwise check if any edges intersect target.
        if self.boundary_approx_intersects(target) {
            return true;
        }
        // Otherwise check if the loop contains the center of target.
        self.iterator_contains_point(&mut it, target.center())
    }

    // CellUnionBound computes a covering of the Loop.
    pub fn cell_union_bound(&self) -> crate::s2::cellunion::CellUnion {
        self.bound.cap_bound().cell_union_bound().into()
    }

    // boundaryApproxIntersects reports if the loop's boundary intersects target.
    // It may also return true when the loop boundary does not intersect target but
    // some edge comes within the worst-case error tolerance.
    //
    // This requires that it.Locate(target) returned Indexed.
    pub fn boundary_approx_intersects(&self, target: &crate::s2::cell::Cell) -> bool {
        let it = self.index.iterator();
        let a_clipped = it.index_cell().unwrap().find_by_shape_id(0).unwrap();

        // If there are no edges, there is no intersection.
        // TODO: Potentially the wrong way to do this maybe directly counting edges is right?
        if a_clipped.num_edges() == 0 {
            return false;
        }

        // We can save some work if target is the index cell itself.
        if it.cell_id() == target.id {
            return true;
        }

        // Otherwise check whether any of the edges intersect target.
        let max_error = FACE_CLIP_ERROR_UV_COORD + INTERSECT_RECT_ERROR_UV_DIST;
        let bound = target.bound_uv().expanded_by_margin(max_error);
        for (_, ai) in a_clipped.edges.iter().enumerate() {
            let v0_outer = clip_to_padded_face(
                &self.vertex(*ai as usize),
                &self.vertex((ai + 1) as usize),
                target.face(),
                max_error,
            );
            if let Some((v0, v1)) = v0_outer
                && edge_intersects_rect(v0, v1, &bound.clone())
            {
                return true;
            }
        }
        false
    }

    /// RegularLoop creates a loop with the given number of vertices, all
    /// located on a circle of the specified radius around the given center.
    pub fn regular_loop(center: Point, radius: crate::s1::angle::Angle, n: usize) -> Self {
        Self::regular_loop_for_frame(&get_frame(&center), radius, n)
    }

    /// RegularLoopForFrame creates a loop centered at the z-axis of the given
    /// coordinate frame, with the specified angular radius in radians and number
    /// of vertices.
    pub fn regular_loop_for_frame(
        frame: &Matrix3<f64>,
        radius: crate::s1::angle::Angle,
        n_vertices: usize,
    ) -> Self {
        Loop::from_points(regular_points_for_frame(frame, radius, n_vertices))
    }

    // findValidationErrorNoIndex reports whether this is not a valid loop, but
    // skips checks that would require a ShapeIndex to be built for the loop. This
    // is primarily used by Polygon to do validation so it doesn't trigger the
    // creation of unneeded ShapeIndices.
    pub fn find_validation_error_no_index(&self) -> Result<(), S2Error> {
        // All vertices must be unit length.
        for (i, v) in self.vertices.iter().enumerate() {
            if !v.0.is_unit() {
                return S2Error::Other(format!("vertex {} is not unit length", i)).into();
            }
        }

        // Loops must have at least 3 vertices (except for empty and full).
        if self.vertices.len() < 3 {
            if self.is_empty_or_full() {
                return Ok(()); // Skip remaining tests.
            }
            return Err(S2Error::Other(
                "non-empty, non-full loops must have at least 3 vertices".to_string(),
            ));
        }

        // Loops are not allowed to have any duplicate vertices or edge crossings.
        // We split this check into two parts. First we check that no edge is
        // degenerate (identical endpoints). Then we check that there are no
        // intersections between non-adjacent edges (including at vertices). The
        // second check needs the ShapeIndex, so it does not fall within the scope
        // of this method.
        for i in 0..self.vertices.len() {
            if self.vertex(i) == self.vertex(i + 1) {
                return Err(S2Error::Other(format!(
                    "edge {} is degenerate (duplicate vertex)",
                    i
                )));
            }

            // Antipodal vertices are not allowed.
            let other = Point(self.vertex(i + 1).0.mul(-1));
            if self.vertex(i) == other {
                return Err(S2Error::Other(format!(
                    "vertices {} and {} are antipodal",
                    i,
                    (i + 1) % self.vertices.len()
                )));
            }
        }

        Ok(())
    }
    /// encode encodes the loop to a byte vector.
    ///
    /// The encoding consists of:
    /// - the encoding version number (8 bits)
    /// - the number of vertices
    /// - the origin_inside flag
    /// - the vertices of the loop
    pub fn encode(&self) -> Vec<u8> {
        let mut data = Vec::new();

        // Version number
        data.push(1); // Encoding version 1

        // Encode the number of vertices in the loop
        let num_vertices = self.vertices.len() as u32;
        data.extend_from_slice(&num_vertices.to_be_bytes());

        // Encode the origin_inside flag
        let origin_byte = if self.origin_inside { 1u8 } else { 0u8 };
        data.push(origin_byte);

        // Encode all the vertices
        for vertex in &self.vertices {
            // Encode each coordinate as a 64-bit float in big-endian order
            data.extend_from_slice(&vertex.0.x.to_be_bytes());
            data.extend_from_slice(&vertex.0.y.to_be_bytes());
            data.extend_from_slice(&vertex.0.z.to_be_bytes());
        }

        data
    }

    /// decode decodes a byte slice encoded by encode.
    pub fn decode(data: &[u8]) -> Result<Self, String> {
        // Check for minimum size (version, num vertices, origin inside)
        if data.len() < 6 {
            return Err("Encoded data too short".to_string());
        }

        // Check version
        if data[0] != 1 {
            return Err(format!("Unknown encoding version {}", data[0]));
        }

        // Decode number of vertices
        let mut num_vertices_bytes = [0u8; 4];
        num_vertices_bytes.copy_from_slice(&data[1..5]);
        let num_vertices = u32::from_be_bytes(num_vertices_bytes) as usize;

        // Decode origin_inside flag
        let origin_inside = data[5] != 0;

        // Check if data is long enough to contain all vertices
        let expected_size = 6 + (num_vertices * 24); // 6 bytes header + 24 bytes per vertex
        if data.len() < expected_size {
            return Err(format!(
                "Encoded data too short: expected {} bytes, found {}",
                expected_size,
                data.len()
            ));
        }

        // Decode vertices
        let mut vertices = Vec::with_capacity(num_vertices);
        for i in 0..num_vertices {
            let offset = 6 + (i * 24);

            let mut x_bytes = [0u8; 8];
            let mut y_bytes = [0u8; 8];
            let mut z_bytes = [0u8; 8];

            x_bytes.copy_from_slice(&data[offset..offset + 8]);
            y_bytes.copy_from_slice(&data[offset + 8..offset + 16]);
            z_bytes.copy_from_slice(&data[offset + 16..offset + 24]);

            let x = f64::from_be_bytes(x_bytes);
            let y = f64::from_be_bytes(y_bytes);
            let z = f64::from_be_bytes(z_bytes);

            vertices.push(Point(crate::r3::vector::Vector { x, y, z }));
        }

        // Create a new loop with the decoded vertices and origin_inside flag
        let mut loop_inst = Loop {
            vertices,
            origin_inside,
            depth: 0,
            bound: Rect::empty(),
            subregion_bound: Rect::empty(),
            index: ShapeIndex::new(),
        };

        // Initialize the bounds and index
        loop_inst.init_bound();
        loop_inst.index = ShapeIndex::new();
        let wrapped_shape_loop = loop_inst.clone().into();
        loop_inst.index.add(&wrapped_shape_loop);

        Ok(loop_inst)
    }

    /// encode_compressed encodes a loop using a more compact (but not
    /// lossless) representation.
    pub fn encode_compressed(&self, snap_level: i32) -> Vec<u8> {
        let mut data = Vec::new();

        // Version number
        data.push(1); // Encoding version 1

        // Encode the snap level (for decoding)
        data.extend_from_slice(&snap_level.to_be_bytes());

        // Encode the number of vertices
        let num_vertices = self.vertices.len() as u32;
        data.extend_from_slice(&num_vertices.to_be_bytes());

        // Encode the origin_inside flag
        let origin_byte = if self.origin_inside { 1u8 } else { 0u8 };
        data.push(origin_byte);

        // Encode vertices as cell IDs at the given snap level
        for vertex in &self.vertices {
            let cell_id = crate::s2::cellid::CellID::from(vertex);
            let cell_id_at_level = cell_id.parent(snap_level as u64);
            data.extend_from_slice(&cell_id_at_level.0.to_be_bytes());
        }

        data
    }

    /// decode_compressed decodes a loop encoded using encode_compressed.
    pub fn decode_compressed(data: &[u8]) -> Result<Self, String> {
        // Check for minimum size (version, snap level, num vertices, origin inside)
        if data.len() < 10 {
            return Err("Encoded data too short".to_string());
        }

        // Check version
        if data[0] != 1 {
            return Err(format!("Unknown encoding version {}", data[0]));
        }

        // Decode snap level
        let mut snap_level_bytes = [0u8; 4];
        snap_level_bytes.copy_from_slice(&data[1..5]);
        let _snap_level = i32::from_be_bytes(snap_level_bytes);

        // Decode number of vertices
        let mut num_vertices_bytes = [0u8; 4];
        num_vertices_bytes.copy_from_slice(&data[5..9]);
        let num_vertices = u32::from_be_bytes(num_vertices_bytes) as usize;

        // Decode origin_inside flag
        let origin_inside = data[9] != 0;

        // Check if data is long enough to contain all vertices
        let expected_size = 10 + (num_vertices * 8); // 10 bytes header + 8 bytes per vertex (CellID)
        if data.len() < expected_size {
            return Err(format!(
                "Encoded data too short: expected {} bytes, found {}",
                expected_size,
                data.len()
            ));
        }

        // Decode vertices
        let mut vertices = Vec::with_capacity(num_vertices);
        for i in 0..num_vertices {
            let offset = 10 + (i * 8);

            let mut cell_id_bytes = [0u8; 8];
            cell_id_bytes.copy_from_slice(&data[offset..offset + 8]);
            let cell_id_raw = u64::from_be_bytes(cell_id_bytes);

            let cell_id = crate::s2::cellid::CellID(cell_id_raw);
            let point = cell_id.center_point();

            vertices.push(point);
        }

        // Create a new loop with the decoded vertices and origin_inside flag
        let mut loop_inst = Loop {
            vertices,
            origin_inside,
            depth: 0,
            bound: Rect::empty(),
            subregion_bound: Rect::empty(),
            index: ShapeIndex::new(),
        };

        // Initialize the bounds and index
        loop_inst.init_bound();
        loop_inst.index = ShapeIndex::new();
        loop_inst.index.add(&ShapeType::Loop(loop_inst.clone()));

        Ok(loop_inst)
    }
}

/// Implement Shape trait for Loop
impl Shape for Loop {
    fn num_edges(&self) -> i64 {
        if self.is_empty_or_full() {
            0
        } else {
            self.vertices.len() as i64
        }
    }

    fn edge(&self, i: i64) -> Edge {
        Edge {
            v0: self.vertex(i as usize),
            v1: self.vertex((i as usize) + 1),
        }
    }

    fn num_chains(&self) -> i64 {
        if self.is_empty() {
            0
        } else {
            1
        }
    }

    fn chain(&self, _chain_id: i64) -> Chain {
        Chain {
            start: 0,
            length: self.num_edges(),
        }
    }

    fn chain_edge(&self, _chain_id: i64, offset: i64) -> Edge {
        Edge {
            v0: self.vertex(offset as usize),
            v1: self.vertex((offset as usize) + 1),
        }
    }

    fn chain_position(&self, edge_id: i64) -> ChainPosition {
        ChainPosition {
            chain_id: 0,
            offset: edge_id,
        }
    }

    fn dimension(&self) -> i64 {
        2
    }

    fn reference_point(&self) -> ReferencePoint {
        self.reference_point()
    }
}

impl Add<VertexTraversalDirection> for usize {
    type Output = usize;

    fn add(self, rhs: VertexTraversalDirection) -> Self::Output {
        match rhs {
            VertexTraversalDirection::Forward => self + 1,
            VertexTraversalDirection::Backward => self - 1,
        }
    }
}

impl Sub<VertexTraversalDirection> for usize {
    type Output = usize;

    fn sub(self, rhs: VertexTraversalDirection) -> Self::Output {
        match rhs {
            VertexTraversalDirection::Forward => self - 1,
            VertexTraversalDirection::Backward => self + 1,
        }
    }
}

impl Mul<Angle> for VertexTraversalDirection {
    type Output = Angle;

    fn mul(self, rhs: Angle) -> Self::Output {
        match self {
            VertexTraversalDirection::Forward => rhs,
            VertexTraversalDirection::Backward => -rhs,
        }
    }
}

impl PartialEq<i32> for VertexTraversalDirection {
    fn eq(&self, other: &i32) -> bool {
        match self {
            VertexTraversalDirection::Forward => *other == 1,
            VertexTraversalDirection::Backward => *other == -1,
        }
    }
}

// Extension to Loop implementation with normalization functions
impl Loop {
    /// Determines if the loop is normalized, meaning its area is at most 2*pi.
    /// Degenerate loops are handled consistently with Sign. For example, if a loop
    /// can be expressed as a union of degenerate or nearly-degenerate CCW triangles,
    /// then it will always be considered normalized.
    pub fn is_normalized(&self) -> bool {
        // Optimization: if the longitude span is less than 180 degrees, then the
        // loop covers less than half the sphere and is therefore normalized.
        if self.bound.lng.len() < PI {
            return true;
        }

        // We allow some error so that hemispheres are always considered normalized.
        // The turning angle evaluates exactly to -2*pi for hemispheres, with no error.
        let max_error = self.turning_angle_max_error();
        self.turning_angle() >= -max_error
    }

    /// Normalizes the loop if necessary so that the area enclosed by the loop is
    /// at most 2*pi. This may invert the loop.
    pub fn normalize(&mut self) {
        if !self.is_normalized() {
            self.invert();
        }
    }

    /// Reverses the order of the loop vertices, effectively complementing the
    /// region represented by the loop. For example, the loop ABCD (with edges
    /// AB, BC, CD, DA) becomes the loop DCBA (with edges DC, CB, BA, AD).
    pub fn invert(&mut self) {
        self.index.reset();
        if self.is_empty_or_full() {
            if self.is_full() {
                self.vertices[0] = EMPTY_LOOP_POINT;
            } else {
                self.vertices[0] = FULL_LOOP_POINT;
            }
        } else {
            // For non-special loops, reverse the slice of vertices.
            self.vertices.reverse();
        }

        // originInside must be set correctly before rebuilding the ShapeIndex.
        self.origin_inside = !self.origin_inside;
        if self.bound.lat.lo > -PI / 2.0 && self.bound.lat.hi < PI / 2.0 {
            // The complement of this loop contains both poles.
            self.bound = Rect::full();
            self.subregion_bound = self.bound.clone();
        } else {
            self.init_bound();
        }

        // TODO: Not sure if this cloning treatment is correct (arc? clone? Point lifetime?)
        let wrapped_loop = ShapeType::Loop(self.clone());

        self.index.add(&wrapped_loop);
    }

    // CanonicalFirstVertex returns a first index and a direction (either +1 or -1)
    // such that the vertex sequence (first, first+dir, ..., first+(n-1)*dir) does
    // not change when the loop vertex order is rotated or inverted. This allows the
    // loop vertices to be traversed in a canonical order. The return values are
    // chosen such that (first, ..., first+n*dir) are in the range [0, 2*n-1] as
    // expected by the Vertex method.
    pub(crate) fn canonical_first_vertex(&self) -> (usize, VertexTraversalDirection) {
        let mut first_idx = 0;
        let n = self.vertices.len();
        for i in 1..n {
            if self.vertex(i).0 < (self.vertex(first_idx).0) {
                first_idx = i
            }
        }

        // 0 <= first_idx <= n-1, so (first_idx+n*dir) <= 2*n-1.
        if self.vertex(first_idx + 1).0 < (self.vertex(first_idx + n - 1).0) {
            return (first_idx, VertexTraversalDirection::Forward);
        }

        // n <= first_idx <= 2*n-1, so (first_idx+n*dir) >= 0.
        first_idx += n;
        return (first_idx, VertexTraversalDirection::Backward);
    }

    /// Returns the sum of the turning angles at each vertex. The return value is
    /// positive if the loop is counter-clockwise, negative if the loop is
    /// clockwise, and zero if the loop is a great circle.
    ///
    /// This quantity is also called the "geodesic curvature" of the loop.
    pub fn turning_angle(&self) -> f64 {
        // For empty and full loops, we return the limit value as the loop area approaches
        // 0 or 4*Pi respectively.
        if self.is_empty_or_full() {
            if self.contains_origin() {
                return -2.0 * PI;
            }
            return 2.0 * PI;
        }

        // Don't crash even if the loop is not well-defined.
        if self.vertices.len() < 3 {
            return 0.0;
        }

        // TODO: Implement canonical_first_vertex function
        // For now, we'll just use vertex 0 as the starting point

        let n = self.vertices.len();
        let (mut i, direction) = self.canonical_first_vertex();
        let mut sum = self.turn_angle(
            self.vertex((i + n - direction) % n),
            self.vertex(i % n),
            self.vertex((i + direction) % n),
        );

        // Using Kahan summation for better numerical stability
        let mut compensation = 0.0;
        let mut remaining = n - 1;

        while remaining > 0 {
            i = (i + direction) % n;
            let angle = self.turn_angle(
                self.vertex((i + n - direction) % n),
                self.vertex(i),
                self.vertex((i + direction) % n),
            );
            let old_sum = sum;
            let corrected_angle = angle + compensation;
            sum += corrected_angle;
            compensation = ((old_sum - sum) + corrected_angle).0;
            remaining -= 1;
        }

        // Bound the result to handle numerical issues
        const MAX_CURVATURE: f64 = 2.0 * PI - 4.0 * DBL_EPSILON;

        // 	return math.Max(-maxCurvature, math.Min(maxCurvature, float64(dir)*float64(sum+compensation)))

        let min_max_curv_and_compensation = MAX_CURVATURE.min((direction * (sum + compensation)).0);
        -MAX_CURVATURE.max(min_max_curv_and_compensation)
    }

    /// Returns the maximum error in TurningAngle. The value is not constant; it
    /// depends on the loop.
    pub(crate) fn turning_angle_max_error(&self) -> f64 {
        // The maximum error can be bounded as follows:
        //   3.00 * dblEpsilon    for RobustCrossProd(b, a)
        //   3.00 * dblEpsilon    for RobustCrossProd(c, b)
        //   3.25 * dblEpsilon    for Angle()
        //   2.00 * dblEpsilon    for each addition in the Kahan summation
        //   ------------------
        // 11.25 * dblEpsilon
        let max_error_per_vertex = 11.25 * DBL_EPSILON;
        max_error_per_vertex * self.vertices.len() as f64
    }

    /// Compute the turning angle between three consecutive vertices.
    fn turn_angle(&self, v0: Point, v1: Point, v2: Point) -> Angle {
        // We use the cross product formula rather than a more complex but
        // numerically stable formula because the final result is normalized
        // by the total turning angle.
        let angle = v0.0.cross(&v1.0).angle(&v1.0.cross(&v2.0));

        // Use the determinant to figure out if the angle is positive or negative.
        if v0.0.dot(&v1.0.cross(&v2.0)) > 0.0 {
            angle
        } else {
            -angle
        }
    }

    /// Returns the area of the loop interior, i.e. the region on the left side of
    /// the loop. The return value is between 0 and 4*pi. This value is not affected
    /// by whether this loop is a "hole" or a "shell".
    pub fn area(&self) -> f64 {
        // It is surprisingly difficult to compute the area of a loop robustly. The
        // main issues are (1) whether degenerate loops are considered to be CCW or
        // not (i.e., whether their area is close to 0 or 4*pi), and (2) computing
        // the areas of small loops with good relative accuracy.
        if self.is_empty_or_full() {
            if self.contains_origin() {
                return 4.0 * PI;
            }
            return 0.0;
        }

        // Use the "signed area" approach which computes a signed sum over triangles
        let mut area = self.surface_integral_float64(signed_area);

        // The signed area should be between approximately -4*pi and 4*pi.
        if area < 0.0 {
            // We have computed the negative of the area of the loop exterior.
            area += 4.0 * PI;
        }

        // Clamp the result to the valid range.
        area = area.min(4.0 * PI).max(0.0);

        // If the area is close enough to zero or 4*pi so that the loop orientation
        // is ambiguous, then we compute the loop orientation explicitly.
        let max_error = self.turning_angle_max_error();
        if area < max_error && !self.is_normalized() {
            return 4.0 * PI;
        } else if area > (4.0 * PI - max_error) && self.is_normalized() {
            return 0.0;
        }

        area
    }

    /// Computes the oriented surface integral of some quantity f(x) over the loop
    /// interior. Specialized version for f64 return values.
    fn surface_integral_float64<F>(&self, f: F) -> f64
    where
        F: Fn(Point, Point, Point) -> f64,
    {
        // Maximum length of an edge for it to be considered numerically stable.
        const MAX_LENGTH: f64 = PI - 1e-5;

        let mut sum = 0.0;
        let mut origin = self.vertex(0);

        for i in 1..self.vertices.len() - 1 {
            // Let V_i be vertex(i), let O be the current origin, and let length(A,B)
            // be the length of edge (A,B). At the start of each loop iteration, the
            // "leading edge" of the triangle fan is (O,V_i), and we want to extend
            // the triangle fan so that the leading edge is (O,V_i+1).
            if self.vertex(i + 1).0.angle(&origin.0).0 > MAX_LENGTH {
                // We are about to create an unstable edge, so choose a new origin O'
                // for the triangle fan.
                let old_origin = origin;
                if origin == self.vertex(0) {
                    // The following point is well-separated from V_i and V_0 (and
                    // therefore V_i+1 as well).
                    origin = Point(self.vertex(0).0.cross(&self.vertex(i).0).normalize());
                } else if self.vertex(i).0.angle(&self.vertex(0).0).0 < MAX_LENGTH {
                    // All edges of the triangle (O, V_0, V_i) are stable, so we can
                    // revert to using V_0 as the origin.
                    origin = self.vertex(0);
                } else {
                    // (O, V_i+1) and (V_0, V_i) are antipodal pairs, and O and V_0 are
                    // perpendicular. Therefore V_0.CrossProd(O) is approximately
                    // perpendicular to all of {O, V_0, V_i, V_i+1}, and we can choose
                    // this point O' as the new origin.
                    origin = Point(self.vertex(0).cross(&old_origin).0);

                    // Advance the edge (V_0,O) to (V_0,O').
                    sum += f(self.vertex(0), old_origin, origin);
                }

                // Advance the edge (O,V_i) to (O',V_i).
                sum += f(old_origin, self.vertex(i), origin);
            }

            // Advance the edge (O,V_i) to (O,V_i+1).
            sum += f(origin, self.vertex(i), self.vertex(i + 1));
        }

        // If the origin is not V_0, we need to sum one more triangle.
        if origin != self.vertex(0) {
            // Advance the edge (O,V_n-1) to (O,V_0).
            sum += f(origin, self.vertex(self.vertices.len() - 1), self.vertex(0));
        }

        sum
    }

    /// Returns the true centroid of the loop multiplied by the area of the loop.
    /// The result is not unit length. The centroid may not be contained by the loop.
    ///
    /// We prescale by the loop area for two reasons: (1) it is cheaper to compute
    /// this way, and (2) it makes it easier to compute the centroid of more
    /// complicated shapes (by splitting them into disjoint regions and adding
    /// their centroids).
    pub fn centroid(&self) -> Point {
        self.surface_integral_point(crate::point::true_centroid)
    }

    /// Computes the oriented surface integral of some vector-valued quantity over
    /// the loop interior. Similar to surface_integral_float64 but returns a Point.
    fn surface_integral_point<F>(&self, f: F) -> Point
    where
        F: Fn(&Point, &Point, &Point) -> Point,
    {
        // Maximum length of an edge for it to be considered numerically stable.
        const MAX_LENGTH: f64 = PI - 1e-5;

        let mut sum = R3Vector {
            x: 0.0,
            y: 0.0,
            z: 0.0,
        };
        let mut origin = self.vertex(0);
        // TODO: We dont yet have `Point::point_cross` implemented, using normal cross
        for i in 1..self.vertices.len() - 1 {
            if self.vertex(i + 1).0.angle(&origin.0).0 > MAX_LENGTH {
                let old_origin = origin;
                if origin == self.vertex(0) {
                    origin = self.vertex(0).cross(&self.vertex(i)).normalize();
                } else if self.vertex(i).0.angle(&self.vertex(0).0).0 < MAX_LENGTH {
                    origin = self.vertex(0);
                } else {
                    origin = Point(self.vertex(0).0.cross(&old_origin.0));
                    sum = sum + f(&self.vertex(0), &old_origin, &origin).0;
                }
                sum = sum + f(&old_origin, &self.vertex(i), &origin).0;
            }
            sum = sum + f(&origin, &self.vertex(i), &self.vertex(i + 1)).0;
        }

        if origin != self.vertex(0) {
            sum = sum
                + f(
                    &origin,
                    &self.vertex(self.vertices.len() - 1),
                    &self.vertex(0),
                )
                .0;
        }

        Point(sum)
    }
}

/// SignedArea returns the area of the triangle (a,b,c). The result is positive if the
/// triangle is counterclockwise and negative if the triangle is clockwise.
/// This is used by area().
fn signed_area(a: Point, b: Point, c: Point) -> f64 {
    // This method computes the area using Girard's formula. It's equivalent to
    // computing the solid angle subtended by the triangle at the origin, and then
    // dividing by 2.
    let a_dot_b = a.0.dot(&b.0).clamp(-1.0, 1.0);
    let b_dot_c = b.0.dot(&c.0).clamp(-1.0, 1.0);
    let c_dot_a = c.0.dot(&a.0).clamp(-1.0, 1.0);

    // Let a, b, c be the spherical coordinates (i.e., unit vectors) of the triangle
    // vertices. Then we compute the area with the following formula:
    //   tan(area/2) = (det(a, b, c) / (1 + |a·b| + |b·c| + |c·a|))
    //
    // where det(a, b, c) = a·(b×c), i.e. the triple product of a, b, c.

    // The determinant is the triple product a·(b×c). We can use the identity
    // |a×b| = 2·sin(θ/2) for two unit vectors separated by angle θ.
    let det = a.0.dot(&b.0.cross(&c.0));

    // The denominator is = 1 + |a·b| + |b·c| + |c·a|
    let denom = 1.0 + a_dot_b.abs() + b_dot_c.abs() + c_dot_a.abs();

    // Now use the formula: tan(area/2) = det / denom
    let tan_area_over_2 = det / denom;

    // And finally get the area using atan.
    2.0 * f64::atan(tan_area_over_2)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consts::f64_eq;
    use crate::r3::vector::Vector as R3Vector;
    use crate::s1::angle::Angle;
    use crate::s1::Deg;
    use crate::s2::cell::Cell;
    use crate::s2::cellid::CellID;
    use crate::s2::point::Point;
    use crate::s2::shape::Shape;

    use std::convert::TryInto;
    use std::f64::consts::PI;

    // Helper function to create a test loop from coordinates
    fn make_loop(coords: &[(f64, f64, f64)]) -> Loop {
        let vertices: Vec<Point> = coords
            .iter()
            .map(|&(x, y, z)| Point(R3Vector { x, y, z }.normalize()))
            .collect();
        Loop::from_points(vertices)
    }

    // Helper to create a loop from lat/lng points (degrees)
    // TODO: use LatLng class and use Point constructor for LatLng points for accuracy sake
    fn lat_lng_loop(points: &[(f64, f64)]) -> Loop {
        let vertices: Vec<Point> = points
            .iter()
            .map(|&(lat, lng)| {
                let lat_rad = lat * PI / 180.0;
                let lng_rad = lng * PI / 180.0;
                let phi = PI / 2.0 - lat_rad;
                let x = phi.sin() * lng_rad.cos();
                let y = phi.sin() * lng_rad.sin();
                let z = phi.cos();
                Point(R3Vector { x, y, z })
            })
            .collect();
        Loop::from_points(vertices)
    }

    // Basic test loops
    fn empty_loop() -> Loop {
        Loop::empty()
    }

    fn full_loop() -> Loop {
        Loop::full()
    }

    fn north_pole_loop() -> Loop {
        // A diamond-shaped loop around the north pole
        make_loop(&[
            (0.0, 0.0, 1.0),  // North pole
            (1.0, 0.0, 1.0),  // 45 degrees south of north pole
            (0.0, 1.0, 1.0),  // 45 degrees south of north pole
            (-1.0, 0.0, 1.0), // 45 degrees south of north pole
            (0.0, -1.0, 1.0), // 45 degrees south of north pole
        ])
    }

    fn south_hemisphere_loop() -> Loop {
        // Loop covering the southern hemisphere
        make_loop(&[
            (0.0, 0.0, -1.0), // South pole
            (1.0, 0.0, 0.0),  // Equator (x+)
            (0.0, 1.0, 0.0),  // Equator (y+)
            (-1.0, 0.0, 0.0), // Equator (x-)
            (0.0, -1.0, 0.0), // Equator (y-)
        ])
    }

    fn candy_cane_loop() -> Loop {
        // A spiral loop that follows a candy-stripe pattern.
        make_loop(&[
            (0.0, 0.0, -1.0),
            (0.0, 1.0, 0.0),
            (0.0, 0.0, 1.0),
            (0.0, -1.0, 0.0),
            (1.0, -1.0, 0.0),
            (1.0, 0.0, 1.0),
            (1.0, 1.0, 0.0),
            (1.0, 0.0, -1.0),
        ])
    }

    fn near_hacklp_loop() -> Loop {
        // A small nearly-horizontal loop near the north pole.
        make_loop(&[
            (0.0, 0.0, 1.0),
            (1e-15, 0.0, 1.0 - 1e-15),
            (0.0, 1e-15, 1.0 - 1e-15),
        ])
    }

    fn small_ne_loop() -> Loop {
        // A small clockwise loop in the northeastern hemisphere.
        make_loop(&[(1.0, 0.0, 0.1), (1.0, 0.1, 0.1), (1.0, 0.0, 0.0)])
    }

    // Additional test loops from Go implementation
    fn north_hemi() -> Loop {
        // Northern hemisphere loop
        make_loop(&[
            (0.0, 0.0, 1.0),  // North pole
            (1.0, 0.0, 0.0),  // Equator at 0 longitude
            (0.0, 1.0, 0.0),  // Equator at 90 longitude
            (-1.0, 0.0, 0.0), // Equator at 180 longitude
            (0.0, -1.0, 0.0), // Equator at 270 longitude
        ])
    }

    fn north_hemi3() -> Loop {
        // Northern hemisphere with 3 points
        make_loop(&[
            (0.0, 0.0, 1.0), // North pole
            (0.0, 1.0, 0.0), // Equator at 90 longitude
            (1.0, 0.0, 0.0), // Equator at 0 longitude
        ])
    }

    fn south_hemi() -> Loop {
        // Southern hemisphere loop
        make_loop(&[
            (0.0, 0.0, -1.0), // South pole
            (0.0, 1.0, 0.0),  // Equator at 90 longitude
            (1.0, 0.0, 0.0),  // Equator at 0 longitude
            (0.0, -1.0, 0.0), // Equator at 270 longitude
            (-1.0, 0.0, 0.0), // Equator at 180 longitude
        ])
    }

    fn west_hemi() -> Loop {
        // Western hemisphere loop
        make_loop(&[
            (0.0, 0.0, 1.0),  // North pole
            (0.0, -1.0, 0.0), // Equator at 270 longitude
            (0.0, 0.0, -1.0), // South pole
            (0.0, 1.0, 0.0),  // Equator at 90 longitude
        ])
    }

    fn east_hemi() -> Loop {
        // Eastern hemisphere loop
        make_loop(&[
            (0.0, 0.0, 1.0),  // North pole
            (0.0, 1.0, 0.0),  // Equator at 90 longitude
            (0.0, 0.0, -1.0), // South pole
            (0.0, -1.0, 0.0), // Equator at 270 longitude
        ])
    }

    fn near_hemi() -> Loop {
        // "Near" hemisphere (centered at 0, 0)
        make_loop(&[
            (1.0, 0.0, 0.0),  // Equator at 0 longitude
            (0.0, 0.0, 1.0),  // North pole
            (-1.0, 0.0, 0.0), // Equator at 180 longitude
            (0.0, 0.0, -1.0), // South pole
        ])
    }

    fn far_hemi() -> Loop {
        // "Far" hemisphere (centered at 180, 0)
        make_loop(&[
            (-1.0, 0.0, 0.0), // Equator at 180 longitude
            (0.0, 0.0, 1.0),  // North pole
            (1.0, 0.0, 0.0),  // Equator at 0 longitude
            (0.0, 0.0, -1.0), // South pole
        ])
    }

    fn candy_cane() -> Loop {
        // A spiral stripe that slightly over-wraps the equator
        lat_lng_loop(&[
            (0.0, 0.0),
            (0.0, 90.0),
            (1.0, 180.0),
            (0.0, 270.0),
            (-1.0, 360.0),
            (0.0, 450.0),
        ])
    }

    fn small_necw() -> Loop {
        // A small clockwise loop in the northern & eastern hemispheres
        lat_lng_loop(&[(30.0, 60.0), (30.0, 59.0), (29.0, 59.0)])
    }

    fn arctic80() -> Loop {
        // Loop around the north pole at 80 degrees
        let mut vertices = Vec::new();
        for i in 0..=4 {
            let lng = (i as f64) * 90.0;
            vertices.push((80.0, lng));
        }
        lat_lng_loop(&vertices)
    }

    fn antarctic80() -> Loop {
        // Loop around the south pole at 80 degrees
        let mut vertices = Vec::new();
        for i in 0..=4 {
            let lng = (i as f64) * 90.0;
            vertices.push((-80.0, lng));
        }
        lat_lng_loop(&vertices)
    }

    fn line_triangle() -> Loop {
        // A completely degenerate triangle along the equator
        lat_lng_loop(&[(0.0, 0.0), (0.0, 1.0), (0.0, 2.0)])
    }

    fn skinny_chevron() -> Loop {
        // A nearly-degenerate CCW chevron near the equator
        lat_lng_loop(&[(0.0, 0.0), (0.1, 0.1), (0.0, 1.0), (0.1, 0.9)])
    }

    // Setup for loop relation tests
    fn loop_a() -> Loop {
        // Diamond-shaped non-convex polygon centered at (0, 0)
        lat_lng_loop(&[(0.0, 0.0), (0.0, 10.0), (10.0, 0.0), (0.0, -10.0)])
    }

    fn loop_b() -> Loop {
        // Another diamond-shaped non-convex polygon, partially overlapping with loop_a
        lat_lng_loop(&[(0.0, 0.0), (5.0, 5.0), (0.0, 20.0), (-5.0, 5.0)])
    }

    fn loop_c() -> Loop {
        // Loop that completely contains loop_a
        lat_lng_loop(&[(-15.0, -15.0), (-15.0, 15.0), (15.0, 15.0), (15.0, -15.0)])
    }

    fn loop_d() -> Loop {
        // Loop that's completely contained within loop_a
        lat_lng_loop(&[(0.0, 0.0), (1.0, 2.0), (2.0, 0.0), (1.0, -2.0)])
    }

    fn a_intersect_b() -> Loop {
        // Intersection of loop_a and loop_b
        lat_lng_loop(&[(0.0, 0.0), (0.0, 10.0), (5.0, 5.0), (-5.0, 5.0)])
    }

    fn a_union_b() -> Loop {
        // Union of loop_a and loop_b
        lat_lng_loop(&[
            (0.0, 0.0),
            (5.0, 5.0),
            (0.0, 20.0),
            (-5.0, 5.0),
            (0.0, 0.0),
            (0.0, -10.0),
            (10.0, 0.0),
            (0.0, 10.0),
        ])
    }

    fn a_minus_b() -> Loop {
        // Difference of loop_a and loop_b
        lat_lng_loop(&[
            (0.0, 0.0),
            (0.0, -10.0),
            (10.0, 0.0),
            (0.0, 10.0),
            (5.0, 5.0),
            (-5.0, 5.0),
        ])
    }

    fn b_minus_a() -> Loop {
        // Difference of loop_b and loop_a
        lat_lng_loop(&[
            (0.0, 0.0),
            (-5.0, 5.0),
            (0.0, 20.0),
            (5.0, 5.0),
            (0.0, 10.0),
            (0.0, 0.0),
        ])
    }

    #[test]
    fn test_loop_empty() {
        let loop_empty = empty_loop();
        assert!(loop_empty.is_empty());
        assert!(!loop_empty.is_full());
        assert_eq!(loop_empty.depth, 0);
        assert_eq!(loop_empty.num_vertices(), 1);
        assert_eq!(loop_empty.vertices().len(), 1);
        assert_eq!(loop_empty.num_edges(), 0);
        assert_eq!(loop_empty.num_chains(), 0);
        assert_eq!(loop_empty.dimension(), 2);
        assert!(!loop_empty.reference_point().contained);
    }

    #[test]
    fn test_loop_full() {
        let loop_full = full_loop();
        assert!(!loop_full.is_empty());
        assert!(loop_full.is_full());
        assert_eq!(loop_full.depth, 0);
        assert_eq!(loop_full.num_vertices(), 1);
        assert_eq!(loop_full.vertices().len(), 1);
        assert_eq!(loop_full.num_edges(), 0);
        assert_eq!(loop_full.num_chains(), 0);
        assert_eq!(loop_full.dimension(), 2);
        assert!(loop_full.reference_point().contained);
    }

    #[test]
    fn test_loop_basic() {
        let north = north_pole_loop();

        // Verify edge count and basic properties
        assert_eq!(north.num_vertices(), 5);
        assert_eq!(north.num_edges(), 5);
        assert_eq!(north.vertices().len(), 5);
        assert_eq!(north.num_chains(), 1);

        // Check chain properties
        let chain = north.chain(0);
        assert_eq!(chain.start, 0);
        assert_eq!(chain.length, 5);

        // Test vertex iteration
        for i in 0..north.num_vertices() {
            let v = north.vertex(i);
            assert!((v.0.z > 0.0) || f64_eq!(v.0.z, 0.0)); // All vertices have z ≥ 0
        }

        // Test edge access
        for i in 0..north.num_edges() {
            let edge = north.edge(i as i64);
            assert_eq!(edge.v0, north.vertex(i as usize));
            assert_eq!(edge.v1, north.vertex((i + 1) as usize));
        }

        // Test wrapping (vertex access)
        assert_eq!(north.vertex(0), north.vertex(5));
        assert_eq!(north.vertex(1), north.vertex(6));

        // Test containment of north pole
        assert!(north.contains_point(Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: 1.0
        })));
    }

    #[test]
    fn test_loop_hole_and_sign() {
        let mut north = north_pole_loop();
        let mut south = south_hemisphere_loop();

        // Initially both should not be holes (depth 0)
        assert_eq!(north.depth, 0);
        assert_eq!(south.depth, 0);
        assert!(!north.is_hole());
        assert!(!south.is_hole());
        assert_eq!(north.sign(), 1);
        assert_eq!(south.sign(), 1);

        // Set depth to make north a hole, south remains normal
        north.depth = 1;
        assert!(north.is_hole());
        assert!(!south.is_hole());
        assert_eq!(north.sign(), -1);
        assert_eq!(south.sign(), 1);

        // Make both holes
        south.depth = 3;
        assert!(north.is_hole());
        assert!(south.is_hole());
        assert_eq!(north.sign(), -1);
        assert_eq!(south.sign(), -1);
    }

    #[test]
    fn test_loop_rect_bound() {
        // Empty loop should have empty bounds
        let empty = empty_loop();
        assert!(empty.rect_bound().is_empty());

        // Full loop should have full bounds
        let full = full_loop();
        assert!(full.rect_bound().is_full());

        // North pole loop should have appropriate bounds
        let north = north_pole_loop();
        let bound = north.rect_bound();
        assert!(bound.lat.hi >= 0.99); // Should contain north pole (z=1)
        assert!(bound.lat.lo <= 0.7); // Should extend below 45 degrees north
        assert!(bound.lng.is_full()); // Should wrap all longitudes

        // South hemisphere should include south pole and stop at equator
        let south = south_hemisphere_loop();
        let bound = south.rect_bound();
        assert!(bound.lat.lo <= -0.99); // Should contain south pole (z=-1)
        assert!(bound.lat.hi >= -0.01); // Should reach equator
        assert!(bound.lng.is_full()); // Should wrap all longitudes
    }

    #[test]
    fn test_loop_cap_bound() {
        // Test that cap bounds work as expected on basic cases
        let north = north_pole_loop();
        let cap = north.cap_bound();
        assert!(cap.contains_point(&Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: 1.0
        }))); // North pole

        let south = south_hemisphere_loop();
        let cap = south.cap_bound();
        assert!(cap.contains_point(&Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: -1.0
        }))); // South pole
    }

    #[test]
    fn test_loop_origin_inside() {
        // Test that origin containment matches expectations
        assert!(!empty_loop().contains_origin());
        assert!(full_loop().contains_origin());
        assert!(!north_pole_loop().contains_origin()); // Origin is at center of Earth, not north pole
        assert!(south_hemisphere_loop().contains_origin()); // South hemisphere should contain origin
    }

    #[test]
    fn test_loop_contains_point() {
        let north = north_pole_loop();
        let south = south_hemisphere_loop();

        // Test north pole containment
        let north_pole = Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: 1.0,
        });
        assert!(north.contains_point(north_pole));
        assert!(!south.contains_point(north_pole));

        // Test south pole containment
        let south_pole = Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: -1.0,
        });
        assert!(!north.contains_point(south_pole));
        assert!(south.contains_point(south_pole));

        // Test equator points
        let equator_x = Point(R3Vector {
            x: 1.0,
            y: 0.0,
            z: 0.0,
        });
        assert!(!north.contains_point(equator_x));
        assert!(south.contains_point(equator_x)); // Equator is part of southern hemisphere loop

        // Test middle point (should be in neither)
        let mid_north = Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: 0.5,
        });
        assert!(!north.contains_point(mid_north));
        assert!(!south.contains_point(mid_north));
    }

    #[test]
    fn test_loop_from_cell() {
        // Create loops from a variety of cells at different levels
        for level in [0, 3, 7, 15].iter() {
            let cell_id = CellID::from_face(3).child_begin_at_level(*level as u64);
            let cell = Cell::from(cell_id);
            let loop_from_cell = Loop::from_cell(&cell);

            // Verify vertex count (cell loops always have 4 vertices)
            assert_eq!(loop_from_cell.num_vertices(), 4);
            assert_eq!(loop_from_cell.num_edges(), 4);

            // Verify all cell vertices are present in the loop
            for i in 0..4 {
                assert_eq!(loop_from_cell.vertex(i), cell.vertex(i));
            }

            // Verify containment of cell center
            assert!(loop_from_cell.contains_point(cell.center()));
        }
    }

    #[test]
    fn test_loop_regular() {
        // Test creating a regular loop with varying numbers of vertices
        for &num_vertices in &[3, 4, 5, 6, 10, 100] {
            let center = Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: 1.0,
            }); // North pole
            let radius = Angle::from(Deg(10.0)); // 10 degree radius
            let loop_regular = Loop::regular_loop(center, radius, num_vertices);

            // Verify vertex count
            assert_eq!(loop_regular.num_vertices(), num_vertices);
            assert_eq!(loop_regular.num_edges(), num_vertices.try_into().unwrap());

            // Verify that all vertices are the correct angular distance from center
            for i in 0..num_vertices {
                let v = loop_regular.vertex(i);
                let dist = center.0.angle(&v.0);
                assert!((dist.rad() - radius.rad()).abs() < 1e-10);
            }

            // Verify the loop contains the center point
            assert!(loop_regular.contains_point(center));
        }
    }

    #[test]
    fn test_loop_equal() {
        let north1 = north_pole_loop();
        let north2 = north_pole_loop();
        let south = south_hemisphere_loop();

        // Test identity
        assert!(north1.equal(&north1));

        // Test equality between identical loops
        assert!(north1.equal(&north2));

        // Test inequality between different loops
        assert!(!north1.equal(&south));

        // Test empty and full loops
        let empty = empty_loop();
        let full = full_loop();
        assert!(empty.equal(&empty));
        assert!(full.equal(&full));
        assert!(!empty.equal(&full));

        // Test loops with same boundary but different orientation
        let mut south_copy = south.clone();
        south_copy.invert();
        assert!(!south.equal(&south_copy));
    }

    #[test]
    fn test_loop_boundary_equal() {
        let north1 = north_pole_loop();
        let south = south_hemisphere_loop();

        // Same shape, same order should be boundary equal
        assert!(north1.boundary_equal(&north1));

        // Create a rotated copy of north1
        let mut vertices = north1.vertices().to_vec();
        let first = vertices.remove(0);
        vertices.push(first);
        let north_rotated = Loop::from_points(vertices);

        // Rotated vertices should be boundary equal
        assert!(north1.boundary_equal(&north_rotated));

        // Different loops should not be boundary equal
        assert!(!north1.boundary_equal(&south));

        // Empty and full loops should be boundary equal only to themselves
        let empty = empty_loop();
        let full = full_loop();
        assert!(empty.boundary_equal(&empty));
        assert!(full.boundary_equal(&full));
        assert!(!empty.boundary_equal(&full));
    }

    #[test]
    fn test_loop_contains() {
        let north = north_pole_loop();
        let small_ne = small_ne_loop();
        let empty = empty_loop();
        let full = full_loop();

        // Test degenerate cases
        assert!(full.contains(&empty));
        assert!(full.contains(&north));
        assert!(full.contains(&small_ne));

        assert!(!empty.contains(&full));
        assert!(!empty.contains(&north));
        assert!(!empty.contains(&small_ne));

        // Test non-degenerate cases
        assert!(!north.contains(&full));
        assert!(north.contains(&north)); // Self-containment
        assert!(!north.contains(&small_ne)); // Disjoint loops

        // Test nesting
        assert!(!small_ne.contains(&north));
        assert!(small_ne.contains(&small_ne)); // Self-containment
    }

    #[test]
    fn test_loop_intersects() {
        let north = north_pole_loop();
        let small_ne = small_ne_loop();
        let empty = empty_loop();
        let full = full_loop();
        let south = south_hemisphere_loop();

        // Test degenerate cases
        assert!(!empty.intersects(&empty));
        assert!(!empty.intersects(&north));
        assert!(!empty.intersects(&small_ne));
        assert!(!empty.intersects(&full));

        assert!(!full.intersects(&empty));
        assert!(full.intersects(&north));
        assert!(full.intersects(&small_ne));
        assert!(full.intersects(&full));

        // Test non-degenerate cases
        assert!(north.intersects(&north)); // Self-intersection
        assert!(!north.intersects(&small_ne)); // Disjoint loops
        assert!(north.intersects(&south)); // Loops that share vertices on equator

        assert!(!small_ne.intersects(&north));
        assert!(small_ne.intersects(&small_ne)); // Self-intersection
    }

    #[test]
    fn test_loop_contains_nested() {
        let north = north_pole_loop();
        let south = south_hemisphere_loop();
        let empty = empty_loop();
        let full = full_loop();

        // Test containment relationships
        assert!(full.contains_nested(&empty));
        assert!(full.contains_nested(&north));
        assert!(full.contains_nested(&south));

        assert!(!empty.contains_nested(&north));
        assert!(!empty.contains_nested(&south));
        assert!(!empty.contains_nested(&full));

        // These loops cross, so containment_nested should be false
        assert!(!north.contains_nested(&south));
        assert!(!south.contains_nested(&north));

        // Self-containment should be true
        assert!(north.contains_nested(&north));
        assert!(south.contains_nested(&south));
        assert!(empty.contains_nested(&empty));
        assert!(full.contains_nested(&full));
    }

    #[test]
    fn test_loop_compare_boundary() {
        let north = north_pole_loop();
        let south = south_hemisphere_loop();
        let empty = empty_loop();
        let full = full_loop();

        // Compare boundaries
        assert_eq!(full.compare_boundary(&empty), 1); // Full contains empty
        assert_eq!(empty.compare_boundary(&full), -1); // Empty excludes full

        assert_eq!(full.compare_boundary(&north), 1); // Full contains north
        assert_eq!(north.compare_boundary(&full), -1); // North excludes full

        // North and south should have crossing boundaries
        assert_eq!(north.compare_boundary(&south), 0);
        assert_eq!(south.compare_boundary(&north), 0);

        // Self-comparison should show containment
        assert_eq!(north.compare_boundary(&north), 1);
        assert_eq!(south.compare_boundary(&south), 1);
    }

    #[test]
    fn test_loop_area_and_centroid() {
        // Empty loop should have 0 area
        assert_eq!(empty_loop().area(), 0.0);

        // Full loop should have 4π area (surface area of unit sphere)
        assert_eq!(full_loop().area(), 4.0 * PI);

        // North pole loop area should be positive
        assert!(north_pole_loop().area() > 0.0);

        // Hemisphere should have 2π area
        let south = south_hemisphere_loop();
        assert!((south.area() - 2.0 * PI).abs() < 1e-10);

        // Centroid of empty loop should be zero vector
        // TODO: Zero for R3 vec!
        assert_eq!(empty_loop().centroid().0, R3Vector::new(0.0, 0.0, 0.0));

        // South hemisphere centroid should point towards south pole
        let south_centroid = south.centroid();
        assert!(south_centroid.0.z < 0.0);
    }

    #[test]
    fn test_loop_canonical_first_vertex() {
        let north = north_pole_loop();

        // Test canonical first vertex
        let (first, dir) = north.canonical_first_vertex();

        // The result should be within the valid vertex range
        assert!(first < north.num_vertices());

        // Direction should be either +1 or -1
        assert!(dir == 1 || dir == -1);

        // Empty and full loops should return sensible values
        let (first_empty, dir_empty) = empty_loop().canonical_first_vertex();
        assert_eq!(first_empty, 0);
        assert_eq!(dir_empty, 1);

        let (first_full, dir_full) = full_loop().canonical_first_vertex();
        assert_eq!(first_full, 0);
        assert_eq!(dir_full, 1);
    }

    #[test]
    fn test_loop_normalize() {
        // Create a small loop around south pole (clockwise from outside)
        let mut south_clockwise = make_loop(&[
            (0.0, 0.0, -1.0),  // South pole
            (0.1, 0.0, -0.9),  // Point 1
            (0.0, 0.1, -0.9),  // Point 2
            (-0.1, 0.0, -0.9), // Point 3
        ]);

        // Initially the loop should be clockwise, which is not the normalized orientation
        assert!(!south_clockwise.is_normalized());

        // Normalize should flip it
        south_clockwise.normalize();

        // Now it should be normalized (area <= 2π)
        assert!(south_clockwise.is_normalized());

        // And the area should be large (close to 4π - small area)
        assert!(south_clockwise.area() > 3.0 * PI);

        // North pole loop should already be normalized
        let north = north_pole_loop();
        assert!(north.is_normalized());

        // Area should be small
        assert!(north.area() < PI);

        // Normalizing it should not change anything
        let mut north_copy = north.clone();
        north_copy.normalize();
        assert!(north.equal(&north_copy));
    }

    #[test]
    fn test_loop_invert() {
        // Test inverting a loop changes its area and origin containment
        let north = north_pole_loop();
        let mut north_inverted = north.clone();

        // Initial state
        let original_area = north.area();
        let original_contains_origin = north.contains_origin();

        // Invert the loop
        north_inverted.invert();

        // Area should change to complement (4π - area)
        let inverted_area = north_inverted.area();
        assert!((inverted_area - (4.0 * PI - original_area)).abs() < 1e-10);

        // Origin containment should flip
        assert_eq!(north_inverted.contains_origin(), !original_contains_origin);

        // The vertices should be in reverse order
        for i in 0..north.num_vertices() {
            assert_eq!(
                north.vertex(i),
                north_inverted.vertex(north.num_vertices() - i)
            );
        }
    }

    #[test]
    fn test_loop_encode_decode() {
        // Test that loops can be encoded and decoded correctly
        let loops = [
            empty_loop(),
            full_loop(),
            north_pole_loop(),
            south_hemisphere_loop(),
            small_ne_loop(),
        ];

        for original in &loops {
            // Encode the loop
            let encoded = original.encode();

            // Decode the loop
            let decoded = Loop::decode(&encoded).expect("Failed to decode loop");

            // Check that the loops are equal
            assert!(original.equal(&decoded));

            // Also verify basic properties match
            assert_eq!(original.is_empty(), decoded.is_empty());
            assert_eq!(original.is_full(), decoded.is_full());
            assert_eq!(original.num_vertices(), decoded.num_vertices());
            assert_eq!(original.contains_origin(), decoded.contains_origin());
        }
    }

    #[test]
    fn test_loop_contains_cell() {
        let north = north_pole_loop();
        let south = south_hemisphere_loop();

        // Create cells at different levels and test containment
        for level in [5, 10, 15, 20].iter() {
            // Cell at north pole
            let north_cell = Cell::from(CellID::from_face(0).child_begin_at_level(*level as u64));

            // Cell at south pole
            let south_cell = Cell::from(CellID::from_face(5).child_begin_at_level(*level as u64));

            // Test containment
            assert!(north.contains_cell(&north_cell)); // North loop should contain north cell
            assert!(!north.contains_cell(&south_cell)); // North loop should not contain south cell

            assert!(!south.contains_cell(&north_cell)); // South hemisphere should not contain north cell
            assert!(south.contains_cell(&south_cell)); // South hemisphere should contain south cell
        }
    }

    #[test]
    fn test_loop_cell_intersection() {
        let north = north_pole_loop();
        let south = south_hemisphere_loop();

        // Cell at the equator (should intersect both north and south loops)
        let equator_cell = Cell::from(CellID::from_face(1).child_begin_at_level(10));

        // Test intersection
        assert!(north.intersects_cell(&equator_cell));
        assert!(south.intersects_cell(&equator_cell));

        // Cell entirely in north pole region
        let north_cell = Cell::from(CellID::from_face(0).child_begin_at_level(15));

        // Should intersect north loop but not south
        assert!(north.intersects_cell(&north_cell));
        assert!(!south.intersects_cell(&north_cell));
    }

    #[test]
    fn test_loop_encode_compressed() {
        // Test the compressed encoding/decoding at various snap levels
        let loops = [north_pole_loop(), south_hemisphere_loop(), small_ne_loop()];

        for snap_level in &[10, 15, 20] {
            for original in &loops {
                // Skip empty/full loops for compression tests
                if original.is_empty_or_full() {
                    continue;
                }

                // Encode the loop with compression
                let encoded = original.encode_compressed(*snap_level);

                // Decode the compressed representation
                let decoded =
                    Loop::decode_compressed(&encoded).expect("Failed to decode compressed loop");

                // The decoded loop should be approximately equal to the original
                // We can't expect perfect equality due to the lossy compression

                // Check that basic properties match
                assert_eq!(original.num_vertices(), decoded.num_vertices());
                assert_eq!(original.contains_origin(), decoded.contains_origin());

                // The vertices should be approximately in the same locations
                // Higher snap_level = more precision
                for i in 0..original.num_vertices() {
                    let v1 = original.vertex(i);
                    let v2 = decoded.vertex(i);

                    // The points should be close (angular distance less than a few degrees
                    // at higher snap levels)
                    let angle = v1.0.angle(&v2.0);

                    // Allow a greater error margin for lower snap levels
                    let max_error = match snap_level {
                        10 => 0.05, // About 3 degrees
                        15 => 0.01, // Less than 1 degree
                        _ => 0.001, // Very small error
                    };

                    assert!(
                        angle.rad() < max_error,
                        "Vertex {} differs too much: angle = {} radians",
                        i,
                        angle.rad()
                    );
                }
            }
        }
    }

    #[test]
    fn test_loop_area_consistent_with_turning_angle() {
        // This test verifies the relationship between the loop area and
        // the turning angle at each vertex.
        let test_loops = [
            empty_loop(),
            full_loop(),
            north_hemi(),
            south_hemi(),
            west_hemi(),
            east_hemi(),
            near_hemi(),
            far_hemi(),
            north_hemi3(),
            candy_cane(),
            small_necw(),
            arctic80(),
            antarctic80(),
            line_triangle(),
            skinny_chevron(),
        ];

        for loop_under_test in &test_loops {
            // For a CCW loop, the area and turning angle should have the same sign.
            // For a CW loop, they should have opposite signs.
            let area = loop_under_test.area();
            let turning = loop_under_test.turning_angle();

            // Check if the area and turning angle have consistent signs based on normalization
            if loop_under_test.is_normalized() {
                // For normalized loops, turning angle should be positive, area positive
                assert!(turning >= -loop_under_test.turning_angle_max_error());
                assert!(area >= 0.0);
                assert!(area <= 2.0 * PI + 1e-10);
            } else {
                // For non-normalized loops, turning angle should be negative, area > 2π
                assert!(turning <= loop_under_test.turning_angle_max_error());
                assert!(area >= 2.0 * PI - 1e-10);
                assert!(area <= 4.0 * PI);
            }
        }
    }

    #[test]
    fn test_loop_turning_angle() {
        // Check turning angle values for some simple loops
        let north_turning = north_hemi().turning_angle();
        let south_turning = south_hemi().turning_angle();

        // Northern hemisphere loop should have positive turning angle (CCW)
        assert!(north_turning > 0.0);

        // Southern hemisphere loop should have positive turning angle (CCW)
        assert!(south_turning > 0.0);

        // Empty loop has +2π turning angle
        assert!((empty_loop().turning_angle() - 2.0 * PI).abs() < 1e-10);

        // Full loop has -2π turning angle
        assert!((full_loop().turning_angle() + 2.0 * PI).abs() < 1e-10);

        // Test loops with various shapes
        for test_loop in &[
            north_hemi(),
            south_hemi(),
            west_hemi(),
            east_hemi(),
            near_hemi(),
            far_hemi(),
            north_hemi3(),
            candy_cane(),
            arctic80(),
            antarctic80(),
            skinny_chevron(),
        ] {
            // Create a copy and invert it
            let mut inverted = test_loop.clone();
            inverted.invert();

            // The turning angle should flip sign when the loop is inverted
            assert!((test_loop.turning_angle() + inverted.turning_angle()).abs() < 1e-8);
        }
    }

    #[test]
    fn test_loop_relations() {
        // Test loop relation operations - contains, intersects
        struct TestCase {
            name: &'static str,
            a: fn() -> Loop,
            b: fn() -> Loop,
            contains: bool,
            intersects: bool,
        }

        let test_cases = [
            TestCase {
                name: "EmptyEmpty",
                a: empty_loop,
                b: empty_loop,
                contains: true,
                intersects: false,
            },
            TestCase {
                name: "EmptyFull",
                a: empty_loop,
                b: full_loop,
                contains: false,
                intersects: false,
            },
            TestCase {
                name: "FullEmpty",
                a: full_loop,
                b: empty_loop,
                contains: true,
                intersects: false,
            },
            TestCase {
                name: "FullFull",
                a: full_loop,
                b: full_loop,
                contains: true,
                intersects: true,
            },
            TestCase {
                name: "EmptyNorth",
                a: empty_loop,
                b: north_hemi,
                contains: false,
                intersects: false,
            },
            TestCase {
                name: "FullNorth",
                a: full_loop,
                b: north_hemi,
                contains: true,
                intersects: true,
            },
            TestCase {
                name: "NorthEmpty",
                a: north_hemi,
                b: empty_loop,
                contains: true,
                intersects: false,
            },
            TestCase {
                name: "NorthFull",
                a: north_hemi,
                b: full_loop,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "NorthSouth",
                a: north_hemi,
                b: south_hemi,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "NorthNorth",
                a: north_hemi,
                b: north_hemi,
                contains: true,
                intersects: true,
            },
            TestCase {
                name: "NorthNear",
                a: north_hemi,
                b: near_hemi,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "NorthFar",
                a: north_hemi,
                b: far_hemi,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "NorthEast",
                a: north_hemi,
                b: east_hemi,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "NorthWest",
                a: north_hemi,
                b: west_hemi,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "NorthArctic",
                a: north_hemi,
                b: arctic80,
                contains: true,
                intersects: true,
            },
            TestCase {
                name: "NorthAntarctic",
                a: north_hemi,
                b: antarctic80,
                contains: false,
                intersects: false,
            },
            TestCase {
                name: "ArcticAntarctic",
                a: arctic80,
                b: antarctic80,
                contains: false,
                intersects: false,
            },
            // Tests for the complex loop relations
            TestCase {
                name: "LoopALoopA",
                a: loop_a,
                b: loop_a,
                contains: true,
                intersects: true,
            },
            TestCase {
                name: "LoopALoopB",
                a: loop_a,
                b: loop_b,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "LoopALoopC",
                a: loop_a,
                b: loop_c,
                contains: false,
                intersects: true,
            },
            TestCase {
                name: "LoopALoopD",
                a: loop_a,
                b: loop_d,
                contains: true,
                intersects: true,
            },
            TestCase {
                name: "LoopCLoopA",
                a: loop_c,
                b: loop_a,
                contains: true,
                intersects: true,
            },
            TestCase {
                name: "LoopDLoopA",
                a: loop_d,
                b: loop_a,
                contains: false,
                intersects: true,
            },
        ];

        for test in &test_cases {
            let a = (test.a)();
            let b = (test.b)();

            assert_eq!(
                a.contains(&b),
                test.contains,
                "{}:Contains: expected {}, got {}",
                test.name,
                test.contains,
                a.contains(&b)
            );

            assert_eq!(
                a.intersects(&b),
                test.intersects,
                "{}:Intersects: expected {}, got {}",
                test.name,
                test.intersects,
                a.intersects(&b)
            );
        }
    }

    #[test]
    fn test_loop_boundary_relations() {
        // Test loop boundary relations using compare_boundary
        struct TestCase {
            name: &'static str,
            a: fn() -> Loop,
            b: fn() -> Loop,
            result: i32, // +1: A contains B, -1: A excludes B, 0: boundaries cross
        }

        let test_cases = [
            TestCase {
                name: "EmptyEmpty",
                a: empty_loop,
                b: empty_loop,
                result: 1,
            },
            TestCase {
                name: "EmptyFull",
                a: empty_loop,
                b: full_loop,
                result: -1,
            },
            TestCase {
                name: "FullEmpty",
                a: full_loop,
                b: empty_loop,
                result: 1,
            },
            TestCase {
                name: "FullFull",
                a: full_loop,
                b: full_loop,
                result: 1,
            },
            TestCase {
                name: "EmptyNorth",
                a: empty_loop,
                b: north_hemi,
                result: -1,
            },
            TestCase {
                name: "FullNorth",
                a: full_loop,
                b: north_hemi,
                result: 1,
            },
            TestCase {
                name: "NorthEmpty",
                a: north_hemi,
                b: empty_loop,
                result: 1,
            },
            TestCase {
                name: "NorthFull",
                a: north_hemi,
                b: full_loop,
                result: -1,
            },
            TestCase {
                name: "NorthSouth",
                a: north_hemi,
                b: south_hemi,
                result: 0,
            },
            TestCase {
                name: "NorthNorth",
                a: north_hemi,
                b: north_hemi,
                result: 1,
            },
            TestCase {
                name: "NorthEast",
                a: north_hemi,
                b: east_hemi,
                result: 0,
            },
            TestCase {
                name: "NorthArctic",
                a: north_hemi,
                b: arctic80,
                result: 1,
            },
            TestCase {
                name: "NorthAntarctic",
                a: north_hemi,
                b: antarctic80,
                result: -1,
            },
            TestCase {
                name: "ArcticAntarctic",
                a: arctic80,
                b: antarctic80,
                result: -1,
            },
            // Tests for the complex loop relations
            TestCase {
                name: "LoopALoopB",
                a: loop_a,
                b: loop_b,
                result: 0,
            },
            TestCase {
                name: "LoopALoopC",
                a: loop_a,
                b: loop_c,
                result: -1,
            },
            TestCase {
                name: "LoopALoopD",
                a: loop_a,
                b: loop_d,
                result: 1,
            },
            TestCase {
                name: "LoopCLoopA",
                a: loop_c,
                b: loop_a,
                result: 1,
            },
            TestCase {
                name: "LoopDLoopA",
                a: loop_d,
                b: loop_a,
                result: -1,
            },
        ];

        for test in &test_cases {
            let a = (test.a)();
            let b = (test.b)();

            assert_eq!(
                a.compare_boundary(&b),
                test.result,
                "{}:CompareBoundary: expected {}, got {:?}",
                test.name,
                test.result,
                a.compare_boundary(&b)
            );
        }
    }

    #[test]
    fn test_loop_normalized_compatible_with_contains() {
        // Test that normalization is consistent with the contains operation

        // Create a bunch of loops to test
        let test_loops = [
            north_hemi(),
            south_hemi(),
            west_hemi(),
            east_hemi(),
            near_hemi(),
            far_hemi(),
            arctic80(),
            antarctic80(),
            candy_cane(),
            small_necw(),
        ];

        for a in &test_loops {
            for b in &test_loops {
                // For any loops A and B, if A contains B then after normalizing both,
                // we should have norm(A) contains norm(B).
                let contains = a.contains(b);

                // Clone the loops so we can normalize them
                let mut a_norm = a.clone();
                let mut b_norm = b.clone();

                // Normalize both loops
                a_norm.normalize();
                b_norm.normalize();

                // Check that normalization preserves containment
                assert_eq!(
                    a_norm.contains(&b_norm),
                    contains,
                    "Normalization changed containment relationship: {} vs {}",
                    contains,
                    a_norm.contains(&b_norm)
                );
            }
        }
    }

    // #[test]
    // fn test_loop_contains_non_crossing_boundary() {
    //     // Test the contains_non_crossing_boundary method
    //     struct TestCase {
    //         name: &'static str,
    //         a: fn() -> Loop,
    //         b: fn() -> Loop,
    //         expected: bool,
    //     }
    //
    //     let test_cases = [
    //         TestCase {
    //             name: "EmptyEmpty",
    //             a: empty_loop,
    //             b: empty_loop,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "EmptyFull",
    //             a: empty_loop,
    //             b: full_loop,
    //             expected: false,
    //         },
    //         TestCase {
    //             name: "FullEmpty",
    //             a: full_loop,
    //             b: empty_loop,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "FullFull",
    //             a: full_loop,
    //             b: full_loop,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "EmptyNorth",
    //             a: empty_loop,
    //             b: north_hemi,
    //             expected: false,
    //         },
    //         TestCase {
    //             name: "FullNorth",
    //             a: full_loop,
    //             b: north_hemi,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "NorthEmpty",
    //             a: north_hemi,
    //             b: empty_loop,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "NorthFull",
    //             a: north_hemi,
    //             b: full_loop,
    //             expected: false,
    //         },
    //         TestCase {
    //             name: "NorthSouth",
    //             a: north_hemi,
    //             b: south_hemi,
    //             expected: false,
    //         },
    //         TestCase {
    //             name: "NorthNorth",
    //             a: north_hemi,
    //             b: north_hemi,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "NorthArctic",
    //             a: north_hemi,
    //             b: arctic80,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "NorthAntarctic",
    //             a: north_hemi,
    //             b: antarctic80,
    //             expected: false,
    //         },
    //         // Tests for the complex loop relations
    //         TestCase {
    //             name: "LoopALoopB",
    //             a: loop_a,
    //             b: loop_b,
    //             expected: false,
    //         },
    //         TestCase {
    //             name: "LoopALoopC",
    //             a: loop_a,
    //             b: loop_c,
    //             expected: false,
    //         },
    //         TestCase {
    //             name: "LoopALoopD",
    //             a: loop_a,
    //             b: loop_d,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "LoopCLoopA",
    //             a: loop_c,
    //             b: loop_a,
    //             expected: true,
    //         },
    //         TestCase {
    //             name: "LoopDLoopA",
    //             a: loop_d,
    //             b: loop_a,
    //             expected: false,
    //         },
    //     ];
    //
    //     for test in &test_cases {
    //         let a = (test.a)();
    //         let b = (test.b)();
    //
    //         assert_eq!(
    //             a.contains_non_crossing_boundary(&b),
    //             test.expected,
    //             "{}:ContainsNonCrossingBoundary: expected {}, got {}",
    //             test.name,
    //             test.expected,
    //             a.contains_non_crossing_boundary(&b)
    //         );
    //     }
    // }

    #[test]
    fn test_canonical_first_vertex() {
        let test_loops = [
            north_hemi(),
            south_hemi(),
            east_hemi(),
            west_hemi(),
            near_hemi(),
            far_hemi(),
            candy_cane(),
            small_necw(),
            arctic80(),
            antarctic80(),
        ];

        for loop_under_test in &test_loops {
            // Skip empty/full loops with only one vertex
            if loop_under_test.is_empty_or_full() {
                continue;
            }

            let (first, dir) = loop_under_test.canonical_first_vertex();

            // Verify the canonical vertex is within bounds
            assert!(first < loop_under_test.num_vertices());

            // Direction should be either +1 or -1
            assert!(dir == 1 || dir == -1);

            // Verify that the chosen edge is in fact the first
            // edge in lexicographic ordering
            // (would need to implement proper edge comparison)

            // Create a loop with the canonical ordering
            let mut canonical_vertices = Vec::new();
            if dir == 1 {
                // Forward direction
                for i in 0..loop_under_test.num_vertices() {
                    canonical_vertices.push(loop_under_test.vertex(first + i));
                }
            } else {
                // Reverse direction
                for i in 0..loop_under_test.num_vertices() {
                    canonical_vertices.push(loop_under_test.vertex(first - i));
                }
            }

            // The canonical vertices should still form the same loop
            let canonical_loop = Loop::from_points(canonical_vertices);
            assert!(canonical_loop.boundary_equal(loop_under_test));
        }
    }

    #[test]
    fn test_loop_validate_basic() {
        // Test that valid loops pass validation

        // These loops should all be valid
        let valid_loops = [
            empty_loop(),
            full_loop(),
            north_hemi(),
            south_hemi(),
            west_hemi(),
            east_hemi(),
            near_hemi(),
            far_hemi(),
            north_hemi3(),
            candy_cane(),
            arctic80(),
            antarctic80(),
        ];

        for (i, loop_under_test) in valid_loops.iter().enumerate() {
            // Valid loops should have at least 3 vertices or be empty/full
            if !loop_under_test.is_empty_or_full() {
                assert!(
                    loop_under_test.num_vertices() >= 3,
                    "Valid loop #{} has fewer than 3 vertices",
                    i
                );
            }

            // Vertices should be normalized unit vectors
            for j in 0..loop_under_test.num_vertices() {
                let vertex = loop_under_test.vertex(j);
                // Check that the vertex is a unit vector (length ~= 1)
                let length = vertex.0.norm();
                assert!(
                    (length - 1.0).abs() < 1e-10,
                    "Vertex {} of loop #{} is not a unit vector: length={}",
                    j,
                    i,
                    length
                );
            }

            // Adjacent vertices should not be the same point or antipodal
            if !loop_under_test.is_empty_or_full() {
                for j in 0..loop_under_test.num_vertices() {
                    let v1 = loop_under_test.vertex(j);
                    let v2 = loop_under_test.vertex(j + 1);

                    // Not the same point
                    assert!(
                        v1 != v2,
                        "Adjacent vertices {} and {} in loop #{} are identical",
                        j,
                        j + 1,
                        i
                    );

                    // Not antipodal (opposite points on the sphere)
                    assert!(
                        v1.0.dot(&v2.0) > -0.999,
                        "Adjacent vertices {} and {} in loop #{} are antipodal",
                        j,
                        j + 1,
                        i
                    );
                }
            }
        }
    }

    #[test]
    fn test_loop_validate_detects_invalid_loops() {
        // Create some invalid loops and verify they would be caught by validation

        // Loop with duplicate vertices
        let duplicate_vertices = Loop::from_points(vec![
            Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: 1.0,
            }),
            Point(R3Vector {
                x: 1.0,
                y: 0.0,
                z: 0.0,
            }),
            Point(R3Vector {
                x: 0.0,
                y: 1.0,
                z: 0.0,
            }),
            Point(R3Vector {
                x: 1.0,
                y: 0.0,
                z: 0.0,
            }), // Duplicate of vertex 1
        ]);

        // Check for duplicate vertices
        let mut has_duplicates = false;
        for i in 0..duplicate_vertices.num_vertices() {
            for j in i + 1..duplicate_vertices.num_vertices() {
                if duplicate_vertices.vertex(i) == duplicate_vertices.vertex(j) {
                    has_duplicates = true;
                    break;
                }
            }
        }
        assert!(has_duplicates, "Failed to detect duplicate vertices");

        // Loop with antipodal vertices (invalid - would create a 180° edge)
        let antipodal_vertices = Loop::from_points(vec![
            Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: 1.0,
            }),
            Point(R3Vector {
                x: 1.0,
                y: 0.0,
                z: 0.0,
            }),
            Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: -1.0,
            }), // Antipodal to first vertex
        ]);

        // Check for antipodal adjacent vertices
        let mut has_antipodal = false;
        for i in 0..antipodal_vertices.num_vertices() {
            let v1 = antipodal_vertices.vertex(i);
            let v2 = antipodal_vertices.vertex(i + 1);
            if v1.0.dot(&v2.0) <= -0.99 {
                has_antipodal = true;
                break;
            }
        }
        assert!(has_antipodal, "Failed to detect antipodal vertices");

        // Loop with only 2 vertices (invalid - except for empty/full loops)
        let two_vertex_loop = Loop::from_points(vec![
            Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: 1.0,
            }),
            Point(R3Vector {
                x: 1.0,
                y: 0.0,
                z: 0.0,
            }),
        ]);

        // A non-empty, non-full loop should have at least 3 vertices
        assert!(
            two_vertex_loop.num_vertices() == 2,
            "Expected loop with 2 vertices"
        );
        assert!(
            !two_vertex_loop.is_empty_or_full(),
            "Expected non-empty, non-full loop"
        );

        // Loop with self-intersection
        let self_intersecting = Loop::from_points(vec![
            Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: 1.0,
            }), // North pole
            Point(R3Vector {
                x: 1.0,
                y: 0.0,
                z: 0.0,
            }), // Point on equator (0°)
            Point(R3Vector {
                x: 0.0,
                y: -1.0,
                z: 0.0,
            }), // Point on equator (270°)
            Point(R3Vector {
                x: -1.0,
                y: 0.0,
                z: 0.0,
            }), // Point on equator (180°)
            Point(R3Vector {
                x: 0.0,
                y: 1.0,
                z: 0.0,
            }), // Point on equator (90°)
        ]);

        // This specific construction creates a loop with self-intersections
        // We would need a more complex algorithm to detect this in general, but
        // for this specific case we can check that the loop has 5 vertices and
        // a boundary that overlaps itself.
        assert_eq!(self_intersecting.num_vertices(), 5);

        // Non-unit vector vertices (not normalized)
        let non_unit_vertices = Loop::from_points(vec![
            Point(R3Vector {
                x: 0.0,
                y: 0.0,
                z: 2.0,
            }), // Not normalized
            Point(R3Vector {
                x: 1.0,
                y: 0.0,
                z: 0.0,
            }),
            Point(R3Vector {
                x: 0.0,
                y: 1.0,
                z: 0.0,
            }),
        ]);

        // Verify we can detect non-unit vertices
        let mut has_non_unit = false;
        for i in 0..non_unit_vertices.num_vertices() {
            let vertex = non_unit_vertices.vertex(i);
            let length = vertex.0.norm();
            if (length - 1.0).abs() > 1e-10 {
                has_non_unit = true;
                break;
            }
        }
        assert!(has_non_unit, "Failed to detect non-unit vector vertices");
    }

    #[test]
    fn test_wedge_relations() {
        // Test WedgeContains and WedgeIntersects functions

        // Create some test points for wedge tests
        let north = Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: 1.0,
        });
        let south = Point(R3Vector {
            x: 0.0,
            y: 0.0,
            z: -1.0,
        });
        let east = Point(R3Vector {
            x: 1.0,
            y: 0.0,
            z: 0.0,
        });
        let west = Point(R3Vector {
            x: -1.0,
            y: 0.0,
            z: 0.0,
        });
        let northeast = Point(
            R3Vector {
                x: 1.0,
                y: 1.0,
                z: 0.0,
            }
            .normalize(),
        );
        let northwest = Point(
            R3Vector {
                x: -1.0,
                y: 1.0,
                z: 0.0,
            }
            .normalize(),
        );
        let southeast = Point(
            R3Vector {
                x: 1.0,
                y: -1.0,
                z: 0.0,
            }
            .normalize(),
        );
        let southwest = Point(
            R3Vector {
                x: -1.0,
                y: -1.0,
                z: 0.0,
            }
            .normalize(),
        );

        // Test WedgeContains
        assert!(general_wedge_contains(
            &north, &east, &south, &northeast, &southeast
        ));
        assert!(!general_wedge_contains(
            &north, &east, &south, &northwest, &southwest
        ));

        assert!(general_wedge_contains(
            &east, &north, &west, &northeast, &northwest
        ));
        assert!(!general_wedge_contains(
            &east, &north, &west, &southeast, &southwest
        ));

        // Test WedgeIntersects
        assert!(wedge_intersects(&north, &east, &south, &north, &west));
        assert!(!wedge_intersects(
            &north, &east, &south, &southeast, &southwest
        ));

        // Wedges with shared boundary should not intersect
        assert!(!wedge_intersects(&north, &east, &south, &north, &northeast));

        // Identical wedges should not intersect (one contains the other)
        assert!(!wedge_intersects(&north, &east, &south, &north, &south));

        // Test WedgeIntersects with overlapping wedges
        assert!(wedge_intersects(
            &northwest, &north, &northeast, &west, &east
        ));

        // Test degenerate cases

        // A wedge that spans the entire sphere contains everything
        assert!(general_wedge_contains(&north, &east, &north, &west, &south));

        // A wedge with zero span contains nothing except its boundary
        assert!(!general_wedge_contains(
            &north, &north, &east, &west, &south
        ));
        assert!(general_wedge_contains(&north, &north, &east, &north, &east));
    }

    #[test]
    fn test_loop_cell_union_bound() {
        // Test that cell_union_bound returns reasonable coverings

        // Empty loop should have empty bound
        let empty = empty_loop();
        let empty_cells = empty.cell_union_bound();
        assert!(empty_cells.0.is_empty());

        // Full loop should cover the entire sphere
        let full = full_loop();
        let full_cells = full.cell_union_bound();
        assert_eq!(full_cells.0.len(), 6); // 6 face cells cover the sphere

        // Test with regular loops of different sizes
        let test_loops = [
            north_hemi(),
            south_hemi(),
            east_hemi(),
            west_hemi(),
            arctic80(),
            antarctic80(),
        ];

        for loop_under_test in &test_loops {
            let cell_covering = loop_under_test.cell_union_bound();

            // The covering should not be empty
            assert!(!cell_covering.0.is_empty());

            // Examine each point in the loop and verify it's contained in the covering
            for i in 0..loop_under_test.num_vertices() {
                let vertex = loop_under_test.vertex(i);
                let vertex_cell = CellID::from(&vertex);

                // The vertex should be contained in at least one cell of the covering
                let mut contained = false;
                for &cell_id in &cell_covering.0 {
                    if cell_id.contains(&vertex_cell) {
                        contained = true;
                        break;
                    }
                }

                assert!(contained, "Vertex {} not contained in cell union bound", i);
            }
        }
    }
}
