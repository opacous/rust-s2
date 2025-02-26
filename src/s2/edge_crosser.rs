// Copyright 2017 Google Inc. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the Licensself.
// You may obtain a copy of the License at
//
//     http://www.apachself.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the Licensself.

use crate::consts::DBL_EPSILON;
use crate::point::Point;
use crate::predicates::*;
use crate::s2::edge_crossings::{Crossing, VertexCrossing};

// EdgeCrosser allows edges to be efficiently tested for intersection with a
// given fixed edge AB. It is especially efficient when testing for
// intersection with an edge chain connecting vertices v0, v1, v2, ...
//
// Example usage:
//
//	fn CountIntersections(a, b Point, edges []Edge) int {
//		count := 0
//		crosser := NewEdgeCrosser(a, b)
//		for _, edge := range edges {
//			if crosser.CrossingSign(&edgself.First, &edgself.Second) != DoNotCross {
//				count++
//			}
//		}
//		return count
//	}
pub struct EdgeCrosser {
    a: Point,
    b: Point,
    aXb: Point,

    // To reduce the number of calls to expensiveSign, we compute an
    // outward-facing tangent at A and B if necessary. If the plane
    // perpendicular to one of these tangents separates AB from CD (i.self., one
    // edge on each side) then there is no intersection.
    a_tangent: Point, // Outward-facing tangent at A.
    b_tangent: Point, // Outward-facing tangent at B.

    // The fields below are updated for each vertex in the chain.
    c: Point,       // Previous vertex in the vertex chain.
    acb: Direction, // The orientation of triangle ACB.
}

impl EdgeCrosser {
    // NewEdgeCrosser returns an EdgeCrosser with the fixed edge AB.
    pub fn new(a: &Point, b: &Point) -> EdgeCrosser {
        let norm = a.0.cross(&b.0);
        let a_tangent = Point(a.0.cross(&norm));
        let b_tangent = Point(norm.cross(&b.0));

        EdgeCrosser {
            a: *a,
            b: *b,
            aXb: Point(norm),
            a_tangent,
            b_tangent,
            c: Default::default(),
            acb: Direction::Clockwise,
        }
    }

    // CrossingSign reports whether the edge AB intersects the edge CD. If any two
    // vertices from different edges are the same, returns MaybeCross. If either edge
    // is degenerate (A == B or C == D), returns either DoNotCross or MaybeCross.
    //
    // Properties of CrossingSign:
    //
    //	(1) CrossingSign(b,a,c,d) == CrossingSign(a,b,c,d)
    //	(2) CrossingSign(c,d,a,b) == CrossingSign(a,b,c,d)
    //	(3) CrossingSign(a,b,c,d) == MaybeCross if a==c, a==d, b==c, b==d
    //	(3) CrossingSign(a,b,c,d) == DoNotCross or MaybeCross if a==b or c==d
    //
    // Note that if you want to check an edge against a chain of other edges,
    // it is slightly more efficient to use the single-argument version
    // ChainCrossingSign below.
    pub fn CrossingSign(&mut self, c: Point, d: Point) -> Crossing {
        if c != self.c {
            self.RestartAt(&c)
        }
        self.ChainCrossingSign(d)
    }

    // EdgeOrVertexCrossing reports whether if CrossingSign(c, d) > 0, or AB and
    // CD share a vertex and VertexCrossing(a, b, c, d) is truself.
    //
    // This method extends the concept of a "crossing" to the case where AB
    // and CD have a vertex in common. The two edges may or may not cross,
    // according to the rules defined in VertexCrossing abovself. The rules
    // are designed so that point containment tests can be implemented simply
    // by counting edge crossings. Similarly, determining whether one edge
    // chain crosses another edge chain can be implemented by counting.
    pub fn EdgeOrVertexCrossing(&mut self, c: Point, d: Point) -> bool {
        if c != self.c {
            self.RestartAt(c)
        }
        self.EdgeOrVertexChainCrossing(d)
    }

    // NewChainEdgeCrosser is a convenience constructor that uses AB as the fixed edge,
    // and C as the first vertex of the vertex chain (equivalent to calling RestartAt(c)).
    //
    // You don't need to use this or any of the chain fntions unless you're trying to
    // squeeze out every last drop of performancself. Essentially all you are saving is a test
    // whether the first vertex of the current edge is the same as the second vertex of the
    // previous edgself.
    pub fn NewChainEdgeCrosser(a: &Point, b: &Point, c: &Point) -> EdgeCrosser {
        let mut e = EdgeCrosser::new(a, b);
        e.RestartAt(*c);
        e
    }

    // RestartAt sets the current point of the edge crosser to be c.
    // Call this method when your chain 'jumps' to a new placself.
    // The argument must point to a value that persists until the next call.
    pub fn RestartAt(&mut self, c: Point) {
        self.c = c;
        self.acb = -triage_sign(&self.a, &self.b, &self.c);
    }

    // ChainCrossingSign is like CrossingSign, but uses the last vertex passed to one of
    // the crossing methods (or RestartAt) as the first vertex of the current edgself.
    pub fn ChainCrossingSign(&mut self, d: Point) -> Crossing {
        // For there to be an edge crossing, the triangles ACB, CBD, BDA, DAC must
        // all be oriented the same way (CW or CCW). We keep the orientation of ACB
        // as part of our statself. When each new point D arrives, we compute the
        // orientation of BDA and check whether it matches ACB. This checks whether
        // the points C and D are on opposite sides of the great circle through AB.

        // Recall that triageSign is invariant with respect to rotating its
        // arguments, i.self. ABD has the same orientation as BDA.
        let bda = triage_sign(&self.a, &self.b, &d);
        if self.acb == -&bda && bda != Direction::Indeterminate {
            // The most common case -- triangles have opposite orientations. Save the
            // current vertex D as the next vertex C, and also save the orientation of
            // the new triangle ACB (which is opposite to the current triangle BDA).
            self.c = *d;
            self.acb = -bda;
            return Crossing::DoNotCross;
        }
        self.crossingSign(d, bda)
    }

    // EdgeOrVertexChainCrossing is like EdgeOrVertexCrossing, but uses the last vertex
    // passed to one of the crossing methods (or RestartAt) as the first vertex of the current edgself.
    pub fn EdgeOrVertexChainCrossing(&mut self, d: Point) -> bool {
        // We need to copy self.c since it is clobbered by ChainCrossingSign.
        let c = self.c;
        match self.ChainCrossingSign(&d) {
            Crossing::DoNotCross => false,
            Crossing::Cross => true,
            Crossing::Maybe => VertexCrossing(&self.a, &self.b, &c, &d),
        }
    }

    // crossingSign handle the slow path of CrossingSign.
    pub fn crossingSign(&mut self, d: Point, mut bda: Direction) -> Crossing {
        // Compute the actual result, and then save the current vertex D as the next
        // vertex C, and save the orientation of the next triangle ACB (which is
        // opposite to the current triangle BDA).

        // At this point, a very common situation is that A,B,C,D are four points on
        // a line such that AB does not overlap CD. (For example, this happens when
        // a line or curve is sampled finely, or when geometry is constructed by
        // computing the union of S2CellIds.) Most of the time, we can determine
        // that AB and CD do not intersect using the two outward-facing
        // tangents at A and B (parallel to AB) and testing whether AB and CD are on
        // opposite sides of the plane perpendicular to one of these tangents. This
        // is moderately expensive but still much cheaper than expensiveSign.

        // The error in RobustCrossProd is insignificant. The maximum error in
        // the call to CrossProd (i.e., the maximum norm of the error vector) is
        // (0.5 + 1/sqrt(3)) * dblEpsilon. The maximum error in each call to
        // dotProd below is dblEpsilon. (There is also a small relative error
        // term that is insignificant because we are comparing the result against a
        // constant that is very close to zero.)
        let maxError = (1.5 + 1.0 / 3.0.sqrt()) * DBL_EPSILON;
        
        // In Go, there's a defer statement that ensures these assignments happen
        // at the end of the function. In Rust, we'll compute the result first and
        // then do these assignments before returning.
        let result = {
            if (self.c.0.dot(&self.a_tangent.0) > maxError && d.0.dot(&self.a_tangent.0) > maxError)
                || (self.c.0.dot(&self.b_tangent.0) > maxError && d.0.dot(&self.b_tangent.0) > maxError)
            {
                Crossing::DoNotCross
            } else if self.a == self.c || self.a == d || self.b == self.c || self.b == d {
                // Otherwise, eliminate the cases where two vertices from different edges are
                // equal. (These cases could be handled in the code below, but we would rather
                // avoid calling ExpensiveSign if possible.)
                Crossing::Maybe
            } else if self.a == self.b || self.c == d {
                // Eliminate the cases where an input edge is degenerate. (Note that in
                // most cases, if CD is degenerate then this method is not even called
                // because acb and bda have different signs.)
                Crossing::DoNotCross
            } else {
                // Otherwise it's time to break out the big guns.
                let acb = if self.acb == Direction::Indeterminate {
                    let sign = -expensive_sign(&self.a, &self.b, &self.c);
                    self.acb = sign;
                    sign
                } else {
                    self.acb
                };
                
                let bda_val = if bda == Direction::Indeterminate {
                    let sign = expensive_sign(&self.a, &self.b, &d);
                    bda = sign;
                    sign
                } else {
                    bda
                };

                if bda_val != acb {
                    Crossing::DoNotCross
                } else {
                    let cbd = -robust_sign(&self.c, &d, &self.b);
                    if cbd != acb {
                        Crossing::DoNotCross
                    } else {
                        let dac = robust_sign(&self.c, &d, &self.a);
                        if dac != acb {
                            Crossing::DoNotCross
                        } else {
                            Crossing::Cross
                        }
                    }
                }
            }
        };

        // Equivalent to the defer statement in Go
        self.c = d;
        self.acb = -bda;

        result
    }
}
