// Copyright 2017 Google Inc. All rights reserved.
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
use std::ops::{Add, Mul, Sub};
use crate::predicates::*;

use crate::consts::{DBL_EPSILON, EPSILON};
use crate::point::{ordered_ccw, Point};
use crate::r3::precisevector::PreciseVector;
use crate::r3::vector::*;
use crate::s2::edge_crosser::EdgeCrosser;

// intersectionError can be set somewhat arbitrarily, because the algorithm
// uses more precision if necessary in order to achieve the specified error.
// The only strict requirement is that intersectionError >= dblEpsilon
// radians. However, using a larger error tolerance makes the algorithm more
// efficient because it reduces the number of cases where exact arithmetic is
// needed.
static INTERSECTION_ERROR : f64 = 8.0 * DBL_EPSILON;


// intersectionMergeRadius is used to ensure that intersection points that
// are supposed to be coincident are merged back together into a single
// vertex. This is required in order for various polygon operations (union,
// intersection, etc) to work correctly. It is twice the intersection error
// because two coincident intersection points might have errors in
// opposite directions.
static INTERSECTION_MERGE_RADIUS : f64 = 16.0 * DBL_EPSILON;


// A Crossing indicates how edges cross.
#[derive(Debug, Copy, Clone)]
pub enum Crossing {
    Cross,
    Maybe,
    DoNotCross
}
impl Crossing {
// CrossingSign reports whether the edge AB intersects the edge CD.
// If AB crosses CD at a point that is interior to both edges, Cross is returned.
// If any two vertices from different edges are the same it returns MaybeCross.
// Otherwise it returns DoNotCross.
// If either edge is degenerate (A == B or C == D), the return value is MaybeCross
// if two vertices from different edges are the same and DoNotCross otherwise.
//
// Properties of CrossingSign:
//
//	(1) CrossingSign(b,a,c,d) == CrossingSign(a,b,c,d)
//	(2) CrossingSign(c,d,a,b) == CrossingSign(a,b,c,d)
//	(3) CrossingSign(a,b,c,d) == MaybeCross if a==c, a==d, b==c, b==d
//	(3) CrossingSign(a,b,c,d) == DoNotCross or MaybeCross if a==b or c==d
//
// This method implements an exact, consistent perturbation model such
// that no three points are ever considered to be collinear. This means
// that even if you have 4 points A, B, C, D that lie exactly in a line
// (say, around the equator), C and D will be treated as being slightly to
// one side or the other of AB. This is done in a way such that the
// results are always consistent (see RobustSign).
    fn crossing_sign(a: &Point, b: &Point, c: &Point, d: &Point) -> Crossing {
        let mut crosser = EdgeCrosser::NewChainEdgeCrosser(&a, &b, &c);
        crosser.ChainCrossingSign(d)
    }
}

// VertexCrossing reports whether two edges "cross" in such a way that point-in-polygon
// containment tests can be implemented by counting the number of edge crossings.
//
// Given two edges AB and CD where at least two vertices are identical
// (i.e. CrossingSign(a,b,c,d) == 0), the basic rule is that a "crossing"
// occurs if AB is encountered after CD during a CCW sweep around the shared
// vertex starting from a fixed reference point.
//
// Note that according to this rule, if AB crosses CD then in general CD
// does not cross AB. However, this leads to the correct result when
// counting polygon edge crossings. For example, suppose that A,B,C are
// three consecutive vertices of a CCW polygon. If we now consider the edge
// crossings of a segment BP as P sweeps around B, the crossing number
// changes parity exactly when BP crosses BA or BC.
//
// Useful properties of VertexCrossing (VC):
//
//	(1) VC(a,a,c,d) == VC(a,b,c,c) == false
//	(2) VC(a,b,a,b) == VC(a,b,b,a) == true
//	(3) VC(a,b,c,d) == VC(a,b,d,c) == VC(b,a,c,d) == VC(b,a,d,c)
//	(3) If exactly one of a,b equals one of c,d, then exactly one of
//	    VC(a,b,c,d) and VC(c,d,a,b) is true
//
// It is an error to call this method with 4 distinct vertices.
pub fn VertexCrossing(a: &Point, b: &Point, c: &Point, d: &Point) -> bool {
    // If A == B or C == D there is no intersection. We need to check this
    // case first in case 3 or more input points are identical.
    if a == b || c == d {
        return false
    }

    // If any other pair of vertices is equal, there is a crossing if and only
    // if ordered_ccw indicates that the edge AB is further CCW around the
    // shared vertex O (either A or B) than the edge CD, starting from an
    // arbitrary fixed reference point.

    // Optimization: if AB=CD or AB=DC, we can avoid most of the calculations.
    if a == c {
        return (b == d) || ordered_ccw(a.referenceDir(), d, b, a)
    }
    else if b == d {
        return ordered_ccw(b.referenceDir(), c, a, b)
    } else if a == d {
        return (b == c) || ordered_ccw(a.referenceDir(), c, b, a)
    }
    else if b == c {
        return ordered_ccw(b.referenceDir(), d, a, b)
    }

    false
}

// EdgeOrVertexCrossing is a convenience function that calls CrossingSign to
// handle cases where all four vertices are distinct, and VertexCrossing to
// handle cases where two or more vertices are the same. This defines a crossing
// fntion such that point-in-polygon containment tests can be implemented
// by simply counting edge crossings.
fn EdgeOrVertexCrossing(a: &Point, b: &Point, c: &Point, d: &Point) -> bool {
    match Crossing::crossing_sign(a, b, c, d) {
        Crossing::DoNotCross => false,
        Crossing::Cross => true,
        Crossing::Maybe => VertexCrossing(a, b, c, d)
    }
}

// Intersection returns the intersection point of two edges AB and CD that cross
// (CrossingSign(a,b,c,d) == Crossing).
//
// Useful properties of Intersection:
//
//	(1) Intersection(b,a,c,d) == Intersection(a,b,d,c) == Intersection(a,b,c,d)
//	(2) Intersection(c,d,a,b) == Intersection(a,b,c,d)
//
// The returned intersection point X is guaranteed to be very close to the
// true intersection point of AB and CD, even if the edges intersect at a
// very small angle.
fn Intersection(a0: &Point, a1: &Point, b0: &Point, b1: &Point) -> Point {
    // It is difficult to compute the intersection point of two edges accurately
    // when the angle between the edges is very small. Previously we handled
    // this by only guaranteeing that the returned intersection point is within
    // intersectionError of each edge. However, this means that when the edges
    // cross at a very small angle, the computed result may be very far from the
    // true intersection point.
    //
    // Instead this fntion now guarantees that the result is always within
    // intersectionError of the true intersection. This requires using more
    // sophisticated techniques and in some cases extended precision.
    //
    //  - intersectionStable computes the intersection point using
    //    projection and interpolation, taking care to minimize cancellation
    //    error.
    //
    //  - intersectionExact computes the intersection point using precision
    //    arithmetic and converts the final result back to an Point.
    let mut pt= intersectionStable(a0, a1, b0, b1)
        .unwrap_or_else(|e|intersectionExact(a0, a1, b0, b1));

    // Make sure the intersection point is on the correct side of the sphere.
    // Since all vertices are unit length, and edges are less than 180 degrees,
    // (a0 + a1) and (b0 + b1) both have positive dot product with the
    // intersection point.  We use the sum of all vertices to make sure that the
    // result is unchanged when the edges are swapped or reversed.
    if pt.0.dot(&a0.0.add(a1.0.add(b0.0.add(b1.0)))) < 0.0 {
        pt = Point(pt.0.mul(-1));
    }

    pt
}

// Computes the cross product of two vectors, normalized to be unit length.
// Also returns the length of the cross
// product before normalization, which is useful for estimating the amount of
// error in the result.  For numerical stability, the vectors should both be
// approximately unit length.
fn robustNormalWithLength(x: &Vector, y: &Vector) -> (Vector, f64) {
    // This computes 2 * (x.cross(y)), but has much better numerical
    // stability when x and y are unit length.
    let tmp = x.sub(y).cross(&x.add(y));
    let length = tmp.norm();
    if length != 0 {
        (tmp.mul(1.0 / length), 0.5 * length)
    } else {
        (Vector::default(), 0.5 * length)
    }
}

/*
// intersectionSimple is not used by the C++ so it is skipped here.
*/

// projection returns the projection of aNorm onto X (x.dot(aNorm)), and a bound
// on the error in the result. aNorm is not necessarily unit length.
//
// The remaining parameters (the length of aNorm (aNormLen) and the edge endpoints
// a0 and a1) allow this dot product to be computed more accurately and efficiently.
fn projection(x: &Vector, aNorm: &Vector, aNormLen: f64, a0: &Point, a1: &Point) -> (f64, f64) {
    // The error in the dot product is proportional to the lengths of the input
    // vectors, so rather than using x itself (a unit-length vector) we use
    // the vectors from x to the closer of the two edge endpoints. This
    // typically reduces the error by a huge factor.
    let x0 = x.sub(a0.0);
    let x1 = x.sub(a1.0);
    let x0Dist2 = x0.norm2();
    let x1Dist2 = x1.norm2();

    // If both distances are the same, we need to be careful to choose one
    // endpoint deterministically so that the result does not change if the
    // order of the endpoints is reversed.
    let mut dist = 0.0;
    let mut proj = 0.0;


    if x0Dist2 < x1Dist2 || (x0Dist2 == x1Dist2 && x0.cmp(&x1) == Ordering::Less) {
        dist = x0Dist2.sqrt();
        proj = x0.dot(&aNorm);
    } else {
        dist = x1Dist2.sqrt();
        proj = x1.dot(&aNorm)
    }

    // This calculation bounds the error from all sources: the computation of
    // the normal, the subtraction of one endpoint, and the dot product itself.
    // dblError appears because the input points are assumed to be
    // normalized in double precision.
    //
    // For reference, the bounds that went into this calculation are:
    // ||N'-N|| <= ((1 + 2 * sqrt(3))||N|| + 32 * sqrt(3) * dblError) * epsilon
    // |(A.B)'-(A.B)| <= (1.5 * (A.B) + 1.5 * ||A|| * ||B||) * epsilon
    // ||(X-Y)'-(X-Y)|| <= ||X-Y|| * epsilon
    let bound = (((3.5+2*3.0.sqrt())*aNormLen+32*3.0.sqrt()*DBL_EPSILON)*dist + 1.5*proj.abs())
        * EPSILON;

    return (proj, bound)
}

// compareEdges reports whether (a0,a1) is less than (b0,b1) with respect to a total
// ordering on edges that is invariant under edge reversals.
fn compareEdges(a0: &Point, a1: &Point, b0: &Point, b1: &Point) -> bool {
    let (a0, a1) = match a0.0.cmp(&a1.0) {
        Ordering::Less => (a0, a1),
        Ordering::Equal => (a1, a0),
        Ordering::Greater => (a1, a0)
    };

    let (b0, b1) = match b0.0.cmp(&b1.0) {
        Ordering::Less => (b0, b1),
        Ordering::Equal => (b1, b0),
        Ordering::Greater => (b1, b0)
    };

    a0.0 < b0.0 || (a0 == b0 && b0.0 < b1.0)
}

// intersectionStable returns the intersection point of the edges (a0,a1) and
// (b0,b1) if it can be computed to within an error of at most intersectionError
// by this fntion.
//
// The intersection point is not guaranteed to have the correct sign because we
// choose to use the longest of the two edges first. The sign is corrected by
// Intersection.
fn intersectionStable(a0: &Point, a1: &Point, b0: &Point, b1: &Point) -> Result<Point, Point> {
    // Sort the two edges so that (a0,a1) is longer, breaking ties in a
    // deterministic way that does not depend on the ordering of the endpoints.
    // This is desirable for two reasons:
    //  - So that the result doesn't change when edges are swapped or reversed.
    //  - It reduces error, since the first edge is used to compute the edge
    //    normal (where a longer edge means less error), and the second edge
    //    is used for interpolation (where a shorter edge means less error).
    let aLen2 = a1.0.sub(a0.0).norm2();
    let bLen2 = b1.0.sub(b0.0).norm2();
    if aLen2 < bLen2 || (aLen2 == bLen2 && compareEdges(a0, a1, b0, b1)) {
        return intersectionStableSorted(b0, b1, a0, a1)
    }

    intersectionStableSorted(a0, a1, b0, b1)
}

// intersectionStableSorted is a helper fntion for intersectionStable.
// It expects that the edges (a0,a1) and (b0,b1) have been sorted so that
// the first edge passed in is longer.
fn intersectionStableSorted(a0: &Point, a1: &Point, b0: &Point, b1: &Point) -> Result<Point,
    Point> {
    let mut pt = Point::default();

    // Compute the normal of the plane through (a0, a1) in a stable way.
    let aNorm = a0.0.sub(a1.0).cross(&a0.0.add(a1.0));
    let aNormLen = aNorm.norm();
    let bLen = b1.sub(b0).norm();

    // Compute the projection (i.e., signed distance) of b0 and b1 onto the
    // plane through (a0, a1).  Distances are scaled by the length of aNorm.
    let (b0Dist, b0Error) = projection(&b0.0, &aNorm, aNormLen, &a0, &a1);
    let (b1Dist, b1Error) = projection(&b1.0, &aNorm, aNormLen, &a0, &a1);

    // The total distance from b0 to b1 measured perpendicularly to (a0,a1) is
    // |b0Dist - b1Dist|.  Note that b0Dist and b1Dist generally have
    // opposite signs because b0 and b1 are on opposite sides of (a0, a1).  The
    // code below finds the intersection point by interpolating along the edge
    // (b0, b1) to a fractional distance of b0Dist / (b0Dist - b1Dist).
    //
    // It can be shown that the maximum error in the interpolation fraction is
    //
    //   (b0Dist * b1Error - b1Dist * b0Error) / (distSum * (distSum - errorSum))
    //
    // We save ourselves some work by scaling the result and the error bound by
    // "distSum", since the result is normalized to be unit length anyway.
    let distSum = (b0Dist - b1Dist).abs();
    let errorSum = b0Error + b1Error;
    if distSum <= errorSum {
        return Err(pt)  // Error is unbounded in this case.
    }

    let x = b1.mul(b0Dist).sub(b0.mul(b1Dist))
    let err = bLen*(b0Dist*b1Error-b1Dist*b0Error).abs()
        / (distSum-errorSum) + 2*distSum*DBL_EPSILON;

    // Finally we normalize the result, compute the corresponding error, and
    // check whether the total error is acceptable.
    let xLen = x.norm();
    if err > (INTERSECTION_ERROR-EPSILON)*xLen {
        return Err(pt)
    }

    Ok(x.mul(1.0 / xLen))
}

// intersectionExact returns the intersection point of (a0, a1) and (b0, b1)
// using precise arithmetic. Note that the result is not exact because it is
// rounded down to double precision at the end. Also, the intersection point
// is not guaranteed to have the correct sign (i.e., the return value may need
// to be negated).
fn intersectionExact(a0: &Point, a1: &Point, b0: &Point, b1: &Point) -> Point {
    // Since we are using presice arithmetic, we don't need to worry about
    // numerical stability.
    let a0P : PreciseVector = a0.0.into();
    let a1P : PreciseVector  = a1.0.into();
    let b0P  : PreciseVector = b0.0.into();
    let b1P  : PreciseVector = b1.0.into();
    let aNormP = a0P.cross(&a1P);
    let bNormP = b0P.cross(&b1P);
    let xP = aNormP.cross(&bNormP);

    // The final Normalize() call is done in double precision, which creates a
    // directional error of up to 2*dblError. (Precise conversion and Normalize()
    // each contribute up to dblError of directional error.)
    let mut x: Vector = xP.into();

    if x == Vector::default() {
        // The two edges are exactly collinear, but we still consider them to be
        // "crossing" because of simulation of simplicity. Out of the four
        // endpoints, exactly two lie in the interior of the other edge. Of
        // those two we return the one that is lexicographically smallest.
        x = Vector::new(10.0, 10.0, 10.0); // Greater than any valid S2Point

        let aNorm = Point(aNormP.into());
        let bNorm = Point(bNormP.into());

        if ordered_ccw(b0, a0, b1, &bNorm) && a0<x{
            return *a0
        }
        if ordered_ccw(b0, a1, b1, &bNorm) && a1<x{
            return *a1
        }
        if ordered_ccw(a0, b0, a1, &aNorm) && b0<x{
            return *b0
        }
        if ordered_ccw(a0, b1, a1, &aNorm) && b1<x {
            return *b1
        }
    }

    Point(x)
}

// AngleContainsVertex reports if the angle ABC contains its vertex B.
// Containment is defined such that if several polygons tile the region around
// a vertex, then exactly one of those polygons contains that vertex.
// Returns false for degenerate angles of the form ABA.
//
// Note that this method is not sufficient to determine vertex containment in
// polygons with duplicate vertices (such as the polygon ABCADE).  Use
// ContainsVertexQuery for such polygons. AngleContainsVertex(a, b, c)
// is equivalent to using ContainsVertexQuery as follows:
//
//	ContainsVertexQuery query(b);
//	query.addEdge(a, -1);  // incoming
//	query.addEdge(c, 1);   // outgoing
//	return query.ContainsVertex() > 0;
//
// Useful properties of AngleContainsVertex:
//
//	(1) AngleContainsVertex(a,b,a) == false
//	(2) AngleContainsVertex(a,b,c) == !AngleContainsVertex(c,b,a) unless a == c
//	(3) Given vertices v_1 ... v_k ordered cyclically CCW around vertex b,
//	    AngleContainsVertex(v_{i+1}, b, v_i) is true for exactly one value of i.
//
// REQUIRES: a != b && b != c
pub fn angle_contains_vertex(a: &Point, b: &Point, c: &Point) -> bool {
    // A loop with consecutive vertices A, B, C contains vertex B if and only if
    // the fixed vector R = referenceDir(B) is contained by the wedge ABC.  The
    // wedge is closed at A and open at C, i.e. the point B is inside the loop
    // if A = R but not if C = R.
    //
    // Note that the test below is written so as to get correct results when the
    // angle ABC is degenerate. If A = C or C = R it returns false, and
    // otherwise if A = R it returns true.
    return !ordered_ccw(&b.ortho(), c, a, b)
}

// TODO(roberts): Differences from C++
// fn RobustCrossProd(a, b Point) Point
// fn symbolicCrossProd(a, b Point) Point
// fn exactCrossProd(a, b Point) Point
// fn SignedVertexCrossing(a, b, c, d Point) int
// fn isNormalizable(p Point) bool
// fn ensureNormalizable(p Point) Point
// fn normalizableFromPrecise(p r3.PreciseVector) Point