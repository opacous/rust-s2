// Copyright 2018 Google Inc. All rights reserved.
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

// This file defines a collection of methods for computing the distance to an edge,
// interpolating along an edge, projecting points onto edges, etc.

use crate::consts::DBL_EPSILON;
use crate::error::S2Result;
use crate::point::Point;
use crate::predicates::sign;
use crate::s1::angle::Angle;
use crate::s1::chordangle::{RIGHT, STRAIGHT};
use crate::s1::ChordAngle;
use crate::s2::edge_crossings::{intersection, Crossing};
use std::ops::{Add, Mul, Sub};

/// Returns the distance of point X from line segment AB.
/// The points are expected to be normalized. The result is very accurate for small
/// distances but may have some numerical error if the distance is large
/// (approximately pi/2 or greater). The case A == B is handled correctly.
pub fn distance_from_segment(x: &Point, a: &Point, b: &Point) -> Angle {
    let (min_dist, _) = update_min_distance(x, a, b, ChordAngle::default(), true);

    min_dist.into()
}

/// Reports whether the distance from X to the edge AB is less
/// than limit. (For less than or equal to, specify limit.successor()).
/// This method is faster than distance_from_segment(). If you want to
/// compare against a fixed Angle, you should convert it to a ChordAngle
/// once and save the value, since this conversion is relatively expensive.
pub fn is_distance_less(x: &Point, a: &Point, b: &Point, limit: ChordAngle) -> bool {
    let (_, less) = update_min_distance(x, a, b, limit, false);
    less
}

/// Checks if the distance from X to the edge AB is less
/// than min_dist, and if so, returns the updated value and true.
/// The case A == B is handled correctly.
///
/// Use this method when you want to compute many distances and keep track of
/// the minimum. It is significantly faster than using distance_from_segment
/// because (1) using ChordAngle is much faster than Angle, and (2) it
/// can save a lot of work by not actually computing the distance when it is
/// obviously larger than the current minimum.
pub fn update_min_distance(
    x: &Point,
    a: &Point,
    b: &Point,
    min_dist: ChordAngle,
    always_update: bool,
) -> (ChordAngle, bool) {
    if let Some(d) = interior_dist(x, a, b, min_dist, always_update) {
        // Minimum distance is attained along the edge interior.
        (d, true)
    } else {
        // Otherwise the minimum distance is to one of the endpoints.
        let xa2 = x.sub(&a).0.norm2();
        let xb2 = x.sub(&b).0.norm2();
        let dist = ChordAngle(xa2.min(xb2));
        if !always_update && dist >= min_dist {
            (min_dist, false)
        } else {
            (dist, true)
        }
    }
}

/// Checks if the distance from X to the edge AB is greater
/// than max_dist, and if so, returns the updated value and true.
/// Otherwise it returns false. The case A == B is handled correctly.
pub fn update_max_distance(
    x: &Point,
    a: &Point,
    b: &Point,
    mut max_dist: ChordAngle,
) -> (ChordAngle, bool) {
    let mut dist = ChordAngle::max(
        Point::chord_angle_between_points(x, a),
        Point::chord_angle_between_points(x, b),
    );
    if dist > RIGHT {
        let (new_dist, _) = update_min_distance(&Point(x.0.mul(-1.0)), a, b, dist, true);
        dist = STRAIGHT - new_dist;
    }
    if max_dist < dist {
        max_dist = dist;
        (max_dist, true)
    } else {
        (max_dist, false)
    }
}

/// Reports whether the minimum distance from X to the edge
/// AB is attained at an interior point of AB (i.e., not an endpoint), and that
/// distance is less than limit. (Specify limit.successor() for less than or equal to).
pub fn is_interior_distance_less(x: &Point, a: &Point, b: &Point, limit: ChordAngle) -> bool {
    update_min_interior_distance(x, a, b, limit).is_some()
}

/// Reports whether the minimum distance from X to AB
/// is attained at an interior point of AB (i.e., not an endpoint), and that distance
/// is less than min_dist. If so, the value of min_dist is updated and Some(new_min_dist) is returned.
/// Otherwise it is unchanged and returns None.
pub fn update_min_interior_distance(
    x: &Point,
    a: &Point,
    b: &Point,
    min_dist: ChordAngle,
) -> Option<ChordAngle> {
    interior_dist(x, a, b, min_dist, false)
}

/// Returns the point along the edge AB that is closest to the point X.
/// The fractional distance of this point along the edge AB can be obtained
/// using distance_fraction.
///
/// This requires that all points are unit length.
pub fn project(x: &Point, a: &Point, b: &Point) -> Point {
    let a_xb = a.cross(&b);
    // Find the closest point to X along the great circle through AB.
    let p = x.sub(&a_xb.mul(x.0.dot(&a_xb.0) / a_xb.0.norm2()));

    // If this point is on the edge AB, then it's the closest point.
    // sign() requires Point arguments
    let p_point = p;
    if sign(&a_xb, a, &p_point) && sign(&p_point, b, &a_xb) {
        return Point(p.0.normalize());
    }

    // Otherwise, the closest point is either A or B.
    if x.sub(&a).0.norm2() <= x.sub(&b).0.norm2() {
        *a
    } else {
        *b
    }
}

/// Returns the distance ratio of the point X along an edge AB.
/// If X is on the line segment AB, this is the fraction T such
/// that X == Interpolate(T, A, B).
///
/// This requires that A and B are distinct.
pub fn distance_fraction(x: &Point, a: &Point, b: &Point) -> f64 {
    let d0 = x.distance(a);
    let d1 = x.distance(b);
    d0.rad() / (d0.rad() + d1.rad())
}

/// Returns the point X along the line segment AB whose distance from A
/// is the given fraction "t" of the distance AB. Does NOT require that "t" be
/// between 0 and 1. Note that all distances are measured on the surface of
/// the sphere, so this is more complicated than just computing (1-t)*a + t*b
/// and normalizing the result.
pub fn interpolate(t: f64, a: &Point, b: &Point) -> Point {
    if t == 0.0 {
        return *a;
    }
    if t == 1.0 {
        return *b;
    }
    let ab = a.distance(b);
    interpolate_at_distance(ab * t, a, b)
}

/// Returns the point X along the line segment AB whose
/// distance from A is the angle ax.
pub fn interpolate_at_distance(ax: Angle, a: &Point, b: &Point) -> Point {
    let a_rad = ax.rad();

    // Use PointCross to compute the tangent vector at A towards B. The
    // result is always perpendicular to A, even if A=B or A=-B, but it is not
    // necessarily unit length. (We effectively normalize it below.)
    let normal = a.cross(&b); // Note: Go uses a.PointCross(b) which might be different? Assuming standard cross product.
    let tangent = normal.cross(&a);

    // Now compute the appropriate linear combination of A and "tangent". With
    // infinite precision the result would always be unit length, but we
    // normalize it anyway to ensure that the error is within acceptable bounds.
    // (Otherwise errors can build up when the result of one interpolation is
    // fed into another interpolation.)
    let tangent_norm = tangent.norm();
    // Handle potential division by zero if a == b or a == -b
    let scale = if tangent_norm == 0.0 {
        0.0
    } else {
        a_rad.sin() / tangent_norm
    };
    Point((a.0.mul(a_rad.cos()).add(tangent.mul(scale).0)).normalize())
}

/// Returns the maximum error in the result of update_min_distance (and the
/// associated functions such as update_min_interior_distance, is_distance_less, etc),
/// assuming that all input points are normalized to within the bounds guaranteed by
/// Vector::normalize. The error can be added or subtracted from a ChordAngle
/// using its expanded method.
pub fn min_update_distance_max_error(dist: ChordAngle) -> f64 {
    // There are two cases for the maximum error in UpdateMinDistance(),
    // depending on whether the closest point is interior to the edge.
    min_update_interior_distance_max_error(dist).max(dist.max_point_error())
}

/// Returns the maximum error in the result of update_min_interior_distance, assuming
/// that all input points are normalized to within the bounds guaranteed by Point's
/// Normalize. The error can be added or subtracted from a ChordAngle using its
/// expanded method.
///
/// Note that accuracy goes down as the distance approaches 0 degrees or 180
/// degrees (for different reasons). Near 0 degrees the error is acceptable
/// for all practical purposes (about 1.2e-15 radians ~= 8 nanometers). For
/// exactly antipodal points the maximum error is quite high (0.5 meters),
/// but this error drops rapidly as the points move away from antipodality
/// (approximately 1 millimeter for points that are 50 meters from antipodal,
/// and 1 micrometer for points that are 50km from antipodal).
///
/// TODO(roberts): Currently the error bound does not hold for edges whose endpoints
/// are antipodal to within about 1e-15 radians (less than 1 micron). This could
/// be fixed by extending PointCross to use higher precision when necessary.
pub fn min_update_interior_distance_max_error(dist: ChordAngle) -> f64 {
    // If a point is more than 90 degrees from an edge, then the minimum
    // distance is always to one of the endpoints, not to the edge interior.
    if dist >= RIGHT {
        return 0.0;
    }

    // This bound includes all source of error, assuming that the input points
    // are normalized. a and b are components of chord length that are
    // perpendicular and parallel to a plane containing the edge respectively.
    let b = 1.0_f64.min(0.5 * dist.0);
    let a = (b * (2.0 - b)).sqrt();
    ((2.5 + 2.0 * 3.0_f64.sqrt() + 8.5 * a) * a
        + (2.0 + 2.0 * 3.0_f64.sqrt() / 3.0 + 6.5 * (1.0 - b)) * b
        + (23.0 + 16.0 / 3.0_f64.sqrt()) * DBL_EPSILON)
        * DBL_EPSILON
}

/// Returns Some(shortest_distance) from point x to edge ab, assuming
/// that the closest point to X is interior to AB. If the closest point is not
/// interior to AB, returns None. If always_update is false, the distance
/// is only returned if it is less than the given min_dist.
fn interior_dist(
    x: &Point,
    a: &Point,
    b: &Point,
    min_dist: ChordAngle,
    always_update: bool,
) -> Option<ChordAngle> {
    // Chord distance squared of x to both end points a and b.
    let xa2 = x.sub(&a).0.norm2();
    let xb2 = x.sub(&b).0.norm2();

    // The closest point on AB could either be one of the two vertices (the
    // vertex case) or in the interior (the interior case). Let C = A x B.
    // If X is in the spherical wedge extending from A to B around the axis
    // through C, then we are in the interior case. Otherwise we are in the
    // vertex case.
    //
    // Check whether we might be in the interior case. For this to be true, XAB
    // and XBA must both be acute angles. Checking this condition exactly is
    // expensive, so instead we consider the planar triangle ABX (which passes
    // through the sphere's interior). The planar angles XAB and XBA are always
    // less than the corresponding spherical angles, so if we are in the
    // interior case then both of these angles must be acute.
    //
    // We check this by computing the squared edge lengths of the planar
    // triangle ABX, and testing whether angles XAB and XBA are both acute using
    // the law of cosines:
    //
    //            | XA^2 - XB^2 | < AB^2      (*)
    //
    // This test must be done conservatively (taking numerical errors into
    // account) since otherwise we might miss a situation where the true minimum
    // distance is achieved by a point on the edge interior.
    // See Go comments for error bound derivation.
    let ab2 = a.sub(&b).0.norm2();
    let max_error = (4.75 * DBL_EPSILON * (xa2 + xb2 + ab2) + 8.0 * DBL_EPSILON * DBL_EPSILON);
    if (xa2 - xb2).abs() >= ab2 + max_error {
        return None;
    }

    // The minimum distance might be to a point on the edge interior. Let R
    // be closest point to X that lies on the great circle through AB. Rather
    // than computing the geodesic distance along the surface of the sphere,
    // instead we compute the "chord length" through the sphere's interior.
    // See Go comments for details on approximation.
    let c = a.cross(&b); // C = A x B
    let c2 = c.0.norm2();
    if c2 == 0.0 {
        // Handle degenerate case A=B or A=-B
        return None;
    }
    let x_dot_c = x.0.dot(&c.0);
    let x_dot_c2 = x_dot_c * x_dot_c;
    if !always_update && x_dot_c2 > c2 * min_dist.0 {
        // The closest point on the great circle AB is too far away. We need to
        // test this using ">" rather than ">=" because the actual minimum bound
        // on the distance is (x_dot_c2 / c2), which can be rounded differently
        // than the (more efficient) multiplicative test above.
        return None;
    }

    // Otherwise we do the exact, more expensive test for the interior case.
    // This test is very likely to succeed because of the conservative planar
    // test we did initially.
    //
    // TODO(roberts): Ensure that the errors in test are accurately reflected in the
    // min_update_interior_distance_max_error.
    let cx = c.cross(&x); // Go uses c.Cross(x.Vector), assuming standard cross
                                   // Check if X projects outside the interior of the edge AB on the great circle.
                                   // a.Sub(x.Vector).Dot(cx) >= 0  <==>  (A-X). (C x X) >= 0
                                   // b.Sub(x.Vector).Dot(cx) <= 0  <==>  (B-X). (C x X) <= 0
    if a.sub(&x).0.dot(&cx.0) >= 0.0 || b.sub(&x).0.dot(&cx.0) <= 0.0 {
        return None;
    }

    // Compute the squared chord length XR^2 = XQ^2 + QR^2 (see Go comments).
    // This calculation has good accuracy for all chord lengths since it
    // is based on both the dot product and cross product (rather than
    // deriving one from the other). However, note that the chord length
    // representation itself loses accuracy as the angle approaches π.
    let cx_norm2 = cx.0.norm2();
    let qr = 1.0 - (cx_norm2 / c2).sqrt(); // qr = 1 - |C x X| / |C|
    let dist_len2 = (x_dot_c2 / c2) + (qr * qr);
    let dist = ChordAngle(dist_len2);

    if !always_update && dist >= min_dist {
        return None;
    }

    Some(dist)
}

/// Computes the minimum distance between the given pair of edges.
/// If the two edges cross, the distance is zero. Returns the minimum distance found
/// so far and true if minDist was updated. The cases a0 == a1 and b0 == b1 are handled correctly.
pub fn update_edge_pair_min_distance(
    a0: &Point,
    a1: &Point,
    b0: &Point,
    b1: &Point,
    mut min_dist: ChordAngle,
) -> (ChordAngle, bool) {
    if min_dist == ChordAngle(0.0) {
        return (min_dist, false);
    }
    if Crossing::crossing_sign(a0, a1, b0, b1) == Crossing::Cross {
        return (ChordAngle(0.0), true);
    }

    // let ok1

    // Otherwise, the minimum distance is achieved at an endpoint of at least
    // one of the two edges. We ensure that all four possibilities are always checked.
    //
    // The calculation below computes each of the six vertex-vertex distances
    // twice (this could be optimized).
    let (d1, ok1) = update_min_distance(a0, b0, b1, min_dist, false);
    min_dist = d1;
    let (d2, ok2) = update_min_distance(a1, b0, b1, min_dist, false);
    min_dist = d2;
    let (d3, ok3) = update_min_distance(b0, a0, a1, min_dist, false);
    min_dist = d3;
    let (d4, ok4) = update_min_distance(b1, a0, a1, min_dist, false);
    min_dist = d4;
    (min_dist, ok1 || ok2 || ok3 || ok4)
}

/// Computes the maximum distance between the given pair of edges.
/// If one edge crosses the antipodal reflection of the other, the distance is pi.
/// Returns the maximum distance found so far and true if max_dist was updated.
pub fn update_edge_pair_max_distance(
    a0: &Point,
    a1: &Point,
    b0: &Point,
    b1: &Point,
    mut max_dist: ChordAngle,
) -> (ChordAngle, bool) {
    if max_dist == STRAIGHT {
        return (max_dist, false);
    }
    if Crossing::crossing_sign(a0, a1, &Point(b0.0.mul(-1.0)), &Point(b1.0.mul(-1.0))) == Crossing::Cross {
        return (STRAIGHT, true);
    }

    // Otherwise, the maximum distance is achieved at an endpoint of at least
    // one of the two edges. We ensure that all four possibilities are always checked.
    //
    // The calculation below computes each of the six vertex-vertex distances
    // twice (this could be optimized).
    let (d1, ok1) = update_max_distance(a0, b0, b1, max_dist);
    max_dist = d1;
    let (d2, ok2) = update_max_distance(a1, b0, b1, max_dist);
    max_dist = d2;
    let (d3, ok3) = update_max_distance(b0, a0, a1, max_dist);
    max_dist = d3;
    let (d4, ok4) = update_max_distance(b1, a0, a1, max_dist);
    max_dist = d4;
    (max_dist, ok1 || ok2 || ok3 || ok4)
}

/// Returns the pair of points (a, b) that achieves the
/// minimum distance between edges a0a1 and b0b1, where a is a point on a0a1 and
/// b is a point on b0b1. If the two edges intersect, a and b are both equal to
/// the intersection point. Handles a0 == a1 and b0 == b1 correctly.
pub fn edge_pair_closest_points(a0: &Point, a1: &Point, b0: &Point, b1: &Point) -> (Point, Point) {
    if Crossing::crossing_sign(a0, a1, b0, b1) == Crossing::Cross {
        let x = intersection(a0, a1, b0, b1);
        return (x, x);
    }

    // We save some work by first determining which vertex/edge pair achieves
    // the minimum distance, and then computing the closest point on that edge.
    let mut min_dist = ChordAngle(f64::MAX); // Initialize with max possible value
    let mut closest_vertex = 0; // 0=a0, 1=a1, 2=b0, 3=b1

    let (d1, _) = update_min_distance(a0, b0, b1, min_dist, true); // Always update first time
    min_dist = d1;

    let (d2, ok2) = update_min_distance(a1, b0, b1, min_dist, false);
    if ok2 {
        min_dist = d2;
        closest_vertex = 1;
    }

    let (d3, ok3) = update_min_distance(b0, a0, a1, min_dist, false);
    if ok3 {
        min_dist = d3;
        closest_vertex = 2;
    }

    let (d4, ok4) = update_min_distance(b1, a0, a1, min_dist, false);
    if ok4 {
        // min_dist = d4; // Not needed, just need to know which case
        closest_vertex = 3;
    }

    match closest_vertex {
        0 => (*a0, project(a0, b0, b1)),
        1 => (*a1, project(a1, b0, b1)),
        2 => (project(b0, a0, a1), *b0),
        3 => (project(b1, a0, a1), *b1),
        _ => panic!("illegal case reached"),
    }
}
