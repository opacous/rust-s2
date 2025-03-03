use crate::cellid::{size_ij, st_to_ij};
use crate::r2::point::Point as R2Point;
use crate::r2::rect::Rect;
use crate::s1::interval::Interval;
use crate::s2;
use crate::s2::cellid::CellID;
use crate::s2::point::Point;
use crate::s2::stuv::{siti_to_st, st_to_uv, uv_to_st};

// Constants used by the PaddedCell.
const SWAP_MASK: u8 = 0x01;
const INVERT_MASK: u8 = 0x02;

// Table to help get the i,j coordinates of the child cell at a given position.
// For each child position pos (0..3) and each parent orientation (0..7),
// posToIJ[orientation][pos] gives the IJNormPos of the child at position pos.
// Each IJNormPos is a 2-bit value where the high bit gives the i-position of
// the child (0=left, 1=right) and the low bit gives the j-position
// (0=bottom, 1=top).
static POS_TO_IJ: [[u8; 4]; 8] = [
    // 0: Normal order: (0,0), (0,1), (1,0), (1,1)
    [0, 1, 2, 3],
    // 1: axes swapped: (0,0), (1,0), (0,1), (1,1)
    [0, 2, 1, 3],
    // 2: i-axis inverted: (1,0), (1,1), (0,0), (0,1)
    [2, 3, 0, 1],
    // 3: i-axis inverted, axes swapped: (1,0), (0,0), (1,1), (0,1)
    [2, 0, 3, 1],
    // 4: j-axis inverted: (0,1), (0,0), (1,1), (1,0)
    [1, 0, 3, 2],
    // 5: j-axis inverted, axes swapped: (0,1), (1,1), (0,0), (1,0)
    [1, 3, 0, 2],
    // 6: i,j axes inverted: (1,1), (1,0), (0,1), (0,0)
    [3, 2, 1, 0],
    // 7: i,j axes inverted, axes swapped: (1,1), (0,1), (1,0), (0,0)
    [3, 1, 2, 0],
];

// Table to invert posToIJ. For each parent orientation (0..7) and
// child ij-position (0..3), ijToPos[orientation][ij] gives the
// position of the child cell (0..3).
static IJ_TO_POS: [[u8; 4]; 8] = [
    // 0: Normal order: (0,0), (0,1), (1,0), (1,1)
    [0, 1, 2, 3],
    // 1: axes swapped: (0,0), (1,0), (0,1), (1,1)
    [0, 2, 1, 3],
    // 2: i-axis inverted: (1,0), (1,1), (0,0), (0,1)
    [2, 3, 0, 1],
    // 3: i-axis inverted, axes swapped: (1,0), (0,0), (1,1), (0,1)
    [1, 3, 0, 2],
    // 4: j-axis inverted: (0,1), (0,0), (1,1), (1,0)
    [1, 0, 3, 2],
    // 5: j-axis inverted, axes swapped: (0,1), (1,1), (0,0), (1,0)
    [2, 0, 3, 1],
    // 6: i,j axes inverted: (1,1), (1,0), (0,1), (0,0)
    [3, 2, 1, 0],
    // 7: i,j axes inverted, axes swapped: (1,1), (0,1), (1,0), (0,0)
    [3, 1, 2, 0],
];

// For each child position (0..3), posToOrientation[pos] gives the change
// in orientation (0..7) to be added to the parent orientation.
static POS_TO_ORIENTATION: [u8; 4] = [
    // (0,0): No change (0)
    0, // (0,1): Output i = input j and output j = input (1-i) (4)
    4, // (1,0): Output i = input (1-j) and output j = input i (0)
    0, // (1,1): Output i = input (1-i) and output j = input (1-j) (4)
    4,
];

// Given a position, posToIJ[orientation][pos] gives the (i,j) coordinates of the child at that
// position in the given orientation. Both i,j are either 0 or 1.
fn pos_to_ij(orientation: u8, pos: u8) -> (u8, u8) {
    let ij = POS_TO_IJ[orientation as usize][pos as usize];
    ((ij >> 1) & 1, ij & 1)
}

// Given a child's (i,j) coordinates, ijToPos[orientation][ij] returns the position of the child.
fn ij_to_pos(orientation: u8, i: u8, j: u8) -> u8 {
    let ij = (i << 1) | j;
    IJ_TO_POS[orientation as usize][ij as usize]
}

// The change in the orientation of the Hilbert curve from the parent to the child is given by
// posToOrientation[pos], where pos is the position of the child (0-3).
fn pos_to_orientation(pos: u8) -> u8 {
    POS_TO_ORIENTATION[pos as usize]
}

/// PaddedCell represents a Cell whose (u,v)-range has been expanded on
/// all sides by a given amount of "padding". Unlike Cell, its methods and
/// representation are optimized for clipping edges against Cell boundaries
/// to determine which cells are intersected by a given set of edges.
#[derive(Debug, Clone)]
pub struct PaddedCell {
    pub(crate) id: CellID,
    padding: f64,
    bound: Rect,
    middle: Option<Rect>, // A rect in (u, v)-space that belongs to all four children.
    i_lo: i32,            // Minimum i-coordinate of this cell before padding
    j_lo: i32,            // Minimum j-coordinate of this cell before padding
    orientation: u8,      // Hilbert curve orientation of this cell.
    level: u8,
}

impl PaddedCell {
    /// Creates a new padded cell with the given padding.
    pub fn from_cell_id(id: CellID, padding: f64) -> Self {
        // Fast path for constructing a top-level face (the most common case).
        if id.is_face() {
            let limit = padding + 1.0;
            let bound =
                Rect::from_points(&[R2Point::new(-limit, limit), R2Point::new(-limit, limit)]);
            let middle = Rect::from_intervals(
                Interval::new(-padding, padding).into(),
                Interval::new(-padding, padding).into(),
            );
            return PaddedCell {
                id,
                padding,
                bound,
                middle: Some(middle),
                i_lo: 0,
                j_lo: 0,
                orientation: (id.face() & 1) as u8,
                level: 0,
            };
        }

        let (face, i, j, orientation) = id.face_ij_orientation();
        let level = id.level() as u8;
        let ij_size = size_ij(level as u64);
        let i_lo = i & -(ij_size as i32);
        let j_lo = j & -(ij_size as i32);

        // Get the bound in (u,v) coordinate space
        let uv_bound = Self::ij_level_to_bound_uv(i, j, level as i32).expanded_by_margin(padding);

        PaddedCell {
            id,
            padding,
            bound: uv_bound,
            middle: None,
            i_lo,
            j_lo,
            orientation: orientation as u8,
            level,
        }
    }

    /// Constructs the child of parent with the given (i,j) index.
    /// The four child cells have indices of (0,0), (0,1), (1,0), (1,1), where the i and j
    /// indices correspond to increasing u- and v-values respectively.
    pub fn from_parent_ij(parent: &PaddedCell, i: u8, j: u8) -> Self {
        // Compute the position and orientation of the child incrementally from the
        // orientation of the parent.
        let pos = ij_to_pos(parent.orientation, i, j);
        let children = parent.id.children();

        let mut cell = PaddedCell {
            id: children[pos as usize],
            padding: parent.padding,
            bound: parent.bound.clone(),
            middle: None,
            orientation: parent.orientation ^ pos_to_orientation(pos),
            level: parent.level + 1,
            i_lo: 0, // Will be set below
            j_lo: 0, // Will be set below
        };

        let ij_size = size_ij(cell.level as u64);
        cell.i_lo = parent.i_lo + (i as i32) * ij_size as i32;
        cell.j_lo = parent.j_lo + (j as i32) * ij_size as i32;

        // For each child, one corner of the bound is taken directly from the parent
        // while the diagonally opposite corner is taken from middle().
        let middle = parent.middle();
        if i == 1 {
            cell.bound.x.lo = middle.x.lo;
        } else {
            cell.bound.x.hi = middle.x.hi;
        }
        if j == 1 {
            cell.bound.y.lo = middle.y.lo;
        } else {
            cell.bound.y.hi = middle.y.hi;
        }

        cell
    }

    /// Converts an (i,j) coordinate and cell level to a CellID.
    fn ij_level_to_bound_uv(i: i32, j: i32, level: i32) -> Rect {
        let ij_size = size_ij(level as u64);
        let i_lo = i & -(ij_size as i32);
        let j_lo = j & -(ij_size as i32);
        let i_hi = i_lo + (ij_size as i32);
        let j_hi = j_lo + (ij_size as i32);

        // Compute the bound in (s,t) space and convert to (u,v) coordinates.
        let u_lo = st_to_uv(siti_to_st(2 * i_lo as u64));
        let u_hi = st_to_uv(siti_to_st(2 * i_hi as u64));
        let v_lo = st_to_uv(siti_to_st(2 * j_lo as u64));
        let v_hi = st_to_uv(siti_to_st(2 * j_hi as u64));

        Rect::from_intervals(
            Interval::new(u_lo, u_hi).into(),
            Interval::new(v_lo, v_hi).into(),
        )
    }

    /// Returns the CellID this padded cell represents.
    pub fn cell_id(&self) -> CellID {
        self.id
    }

    /// Returns the amount of padding on this cell.
    pub fn padding(&self) -> f64 {
        self.padding
    }

    /// Returns the level this cell is at.
    pub fn level(&self) -> u8 {
        self.level
    }

    /// Returns the center of this cell.
    pub fn center(&self) -> Point {
        let ij_size = size_ij(self.level as u64);
        let si = (2 * self.i_lo + ij_size as i32) as u32;
        let ti = (2 * self.j_lo + ij_size as i32) as u32;
        crate::s2::stuv::face_siti_to_xyz(self.id.face(), si.into(), ti as u64).normalize()
    }

    /// Returns the rectangle in the middle of this cell that belongs to
    /// all four of its children in (u,v)-space.
    pub fn middle(&self) -> Rect {
        // We compute this field lazily because it is not needed the majority of the
        // time (i.e., for cells where the recursion terminates).
        if let Some(ref middle) = self.middle {
            return middle.clone();
        }

        let ij_size = size_ij(self.level as u64);
        let u = st_to_uv(siti_to_st((2 * self.i_lo + ij_size as i32) as u64));
        let v = st_to_uv(siti_to_st((2 * self.j_lo + ij_size as i32) as u64));

        let middle = Rect::from_intervals(
            Interval::new(u - self.padding, u + self.padding).into(),
            Interval::new(v - self.padding, v + self.padding).into(),
        );

        // Store the computed middle rect for future use
        let mut cell = self.clone();
        cell.middle = Some(middle.clone());

        middle
    }

    /// Returns the bounds for this cell in (u,v)-space including padding.
    pub fn bound(&self) -> Rect {
        self.bound.clone()
    }

    /// Returns the (i,j) coordinates for the child cell at the given traversal
    /// position. The traversal position corresponds to the order in which child
    /// cells are visited by the Hilbert curve.
    pub fn child_ij(&self, pos: u8) -> (u8, u8) {
        pos_to_ij(self.orientation, pos)
    }

    /// Returns the vertex where the space-filling curve enters this cell.
    pub fn entry_vertex(&self) -> Point {
        // The curve enters at the (0,0) vertex unless the axis directions are
        // reversed, in which case it enters at the (1,1) vertex.
        let mut i = self.i_lo;
        let mut j = self.j_lo;
        if self.orientation & INVERT_MASK != 0 {
            let ij_size = size_ij(self.level as i32 as u64);
            i += ij_size as i32;
            j += ij_size as i32;
        }
        s2::stuv::face_siti_to_xyz(self.id.face(), (2 * i) as u64, (2 * j) as u64).normalize()
    }

    /// Returns the vertex where the space-filling curve exits this cell.
    pub fn exit_vertex(&self) -> Point {
        // The curve exits at the (1,0) vertex unless the axes are swapped or
        // inverted but not both, in which case it exits at the (0,1) vertex.
        let mut i = self.i_lo;
        let mut j = self.j_lo;
        let ij_size = size_ij(self.level as i32 as u64);
        if self.orientation == 0 || self.orientation == SWAP_MASK + INVERT_MASK {
            i += ij_size as i32;
        } else {
            j += ij_size as i32;
        }
        s2::stuv::face_siti_to_xyz(self.id.face(), (2 * i) as u64, (2 * j) as u64).normalize()
    }

    /// Returns the smallest CellID that contains all descendants of this
    /// padded cell whose bounds intersect the given rect. For algorithms that use
    /// recursive subdivision to find the cells that intersect a particular object, this
    /// method can be used to skip all of the initial subdivision steps where only
    /// one child needs to be expanded.
    ///
    /// Note that this method is not the same as returning the smallest cell that contains
    /// the intersection of this cell with rect. Because of the padding, even if one child
    /// completely contains rect it is still possible that a neighboring child may also
    /// intersect the given rect.
    ///
    /// The provided Rect must intersect the bounds of this cell.
    pub fn shrink_to_fit(&self, rect: &Rect) -> CellID {
        // Quick rejection test: if rect contains the center of this cell along
        // either axis, then no further shrinking is possible.
        if self.level == 0 {
            // Fast path (most calls to this function start with a face cell).
            if rect.x.contains(0.0) || rect.y.contains(0.0) {
                return self.id;
            }
        }

        let ij_size = size_ij(self.level as u64);
        if rect.x.contains(st_to_uv(siti_to_st(
            (2 * self.i_lo + ij_size as i32) as u64,
        ))) || rect.y.contains(st_to_uv(siti_to_st(
            (2 * self.j_lo + ij_size as i32) as u64,
        ))) {
            return self.id;
        }

        // Otherwise we expand rect by the given padding on all sides and find
        // the range of coordinates that it spans along the i- and j-axes. We then
        // compute the highest bit position at which the min and max coordinates
        // differ. This corresponds to the first cell level at which at least two
        // children intersect rect.

        // Increase the padding to compensate for the error in uv_to_st.
        // (The constant below is a provable upper bound on the additional error.)
        const DBL_EPSILON: f64 = 2.2204460492503131e-16;
        let padded = rect.expanded_by_margin(self.padding + 1.5 * DBL_EPSILON);

        let mut i_min = self.i_lo;
        let mut j_min = self.j_lo;
        let mut i_xor;
        let mut j_xor;

        // Calculate minimum i-coordinate
        let padded_i_min = st_to_ij(uv_to_st(padded.x.lo));
        if i_min < padded_i_min {
            i_min = padded_i_min;
        }

        // Calculate i_xor (XOR of min and max i-coordinates)
        let i_max_limit = self.i_lo + (ij_size as i32) - 1;
        let padded_i_max = st_to_ij(uv_to_st(padded.x.hi));
        if i_max_limit <= padded_i_max {
            i_xor = i_min ^ i_max_limit;
        } else {
            i_xor = i_min ^ padded_i_max;
        }

        // Calculate minimum j-coordinate
        let padded_j_min = st_to_ij(uv_to_st(padded.y.lo));
        if j_min < padded_j_min {
            j_min = padded_j_min;
        }

        // Calculate j_xor (XOR of min and max j-coordinates)
        let j_max_limit = self.j_lo + (ij_size as i32) - 1;
        let padded_j_max = st_to_ij(uv_to_st(padded.y.hi));
        if j_max_limit <= padded_j_max {
            j_xor = j_min ^ j_max_limit;
        } else {
            j_xor = j_min ^ padded_j_max;
        }

        // Compute the highest bit position where the two i- or j-endpoints differ,
        // and then choose the cell level that includes both of these endpoints.
        let level_msb = ((i_xor | j_xor) << 1) + 1;
        let level = if level_msb == 0 {
            30 // MaxLevel
        } else {
            30 - level_msb.leading_zeros() as u8
        };

        if level <= self.level {
            return self.id;
        }

        CellID::from_face_ij(self.id.face(), i_min, j_min).parent(level as u64)
    }
}

#[cfg(test)]
mod tests {
    use crate::consts::EPSILON;
use crate::s2::stuv::face_siti_to_xyz;
    use super::*;

    #[test]
    fn test_padded_cell_from_cell_id() {
        // Test creating a padded cell from a face cell
        let cell_id = CellID::from_face(1);
        let padding = 0.1;
        let padded_cell = PaddedCell::from_cell_id(cell_id, padding);

        assert_eq!(padded_cell.cell_id(), cell_id);
        assert_eq!(padded_cell.padding(), padding);
        assert_eq!(padded_cell.level(), 0);
        assert_eq!(padded_cell.orientation, 1); // Face 1 has orientation 1

        // Verify the bound is correct for a face cell
        let expected_limit = padding + 1.0;
        assert_eq!(padded_cell.bound.x.lo, -expected_limit);
        assert_eq!(padded_cell.bound.x.hi, expected_limit);
        assert_eq!(padded_cell.bound.y.lo, -expected_limit);
        assert_eq!(padded_cell.bound.y.hi, expected_limit);
    }

    #[test]
    fn test_padded_cell_middle() {
        // Test the middle calculation
        let cell_id = CellID::from_face(0);
        let padding = 0.1;
        let padded_cell = PaddedCell::from_cell_id(cell_id, padding);

        let middle = padded_cell.middle();

        assert_eq!(middle.x.lo, -padding);
        assert_eq!(middle.x.hi, padding);
        assert_eq!(middle.y.lo, -padding);
        assert_eq!(middle.y.hi, padding);
    }

    // #[test]
    // fn test_padded_cell_from_parent_ij() {
    //     // Test creating a child cell from a parent
    //     let parent = PaddedCell::from_cell_id(CellID::from_face(0), 0.1);
    //     let child = PaddedCell::from_parent_ij(&parent, 1, 0);
    //
    //     assert_eq!(child.level(), 1);
    //     assert!(child.cell_id().is_child_of(parent.cell_id()));
    //
    //     // Check that the orientation is updated correctly
    //     assert_eq!(
    //         child.orientation,
    //         parent.orientation ^ pos_to_orientation(ij_to_pos(parent.orientation, 1, 0))
    //     );
    // }

    #[test]
    fn test_padded_cell_vertices() {
        // Test entry and exit vertices
        let cell = PaddedCell::from_cell_id(CellID::from_face(0), 0.1);

        let entry = cell.entry_vertex();
        let exit = cell.exit_vertex();

        // For face 0 with orientation 0, entry should be at (0,0) and exit at (1,0)
        let expected_entry = face_siti_to_xyz(0, 0, 0).normalize();
        assert_f64_eq!(entry.0.x, &expected_entry.0.x);
        assert_f64_eq!(entry.0.y, &expected_entry.0.y);
        assert_f64_eq!(entry.0.z, &expected_entry.0.z);

        let expected_exit = face_siti_to_xyz(0, 2 * size_ij(0), 0).normalize();
        assert_f64_eq!(exit.0.x, &expected_exit.0.x);
        assert_f64_eq!(exit.0.y, &expected_exit.0.y);
        assert_f64_eq!(exit.0.z, &expected_exit.0.z);

    }
}
