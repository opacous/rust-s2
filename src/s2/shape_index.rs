use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Mutex;
use std::collections::BTreeMap;
use crate::consts::DBL_EPSILON;
use crate::r2::rect::Rect as R2Rect;
use crate::r2::Point as R2Point;
use crate::s2::cellid::CellID;
use crate::s2::cell::Cell;
use crate::s2::edge_crosser::EdgeCrosser;
use crate::s2::metric::Metric;
use crate::s2::point::Point;
use crate::s2::region::Region;
use crate::shape::Edge;

// edgeClipErrorUVCoord is the maximum error in a u- or v-coordinate
// compared to the exact result, assuming that the points A and B are in
// the rectangle [-1,1]x[1,1] or slightly outside it (by 1e-10 or less).
pub const EDGE_CLIP_ERROR_UV_COORD: f64 = 2.25 * DBL_EPSILON;

// faceClipErrorUVCoord is the maximum angle between a returned vertex
// and the nearest point on the exact edge AB expressed as the maximum error
// in an individual u- or v-coordinate. In other words, for each
// returned vertex there is a point on the exact edge AB whose u- and
// v-coordinates differ from the vertex by at most this amount.
pub const FACE_CLIP_ERROR_UV_COORD: f64 = 9.0 * (1.0 / std::f64::consts::SQRT_2) * DBL_EPSILON;

// CellRelation describes the possible relationships between a target cell
// and the cells of the ShapeIndex. If the target is an index cell or is
// contained by an index cell, it is Indexed. If the target is subdivided
// into one or more index cells, it is Subdivided. Otherwise it is Disjoint.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CellRelation {
    Indexed,
    Subdivided,
    Disjoint
}

// cellPadding defines the total error when clipping an edge which comes
// from two sources:
// (1) Clipping the original spherical edge to a cube face (the face edge).
//     The maximum error in this step is faceClipErrorUVCoord.
// (2) Clipping the face edge to the u- or v-coordinate of a cell boundary.
//     The maximum error in this step is edgeClipErrorUVCoord.
// Finally, since we encounter the same errors when clipping query edges, we
// double the total error so that we only need to pad edges during indexing
// and not at query time.
pub const CELL_PADDING: f64 = 2.0 * (FACE_CLIP_ERROR_UV_COORD + EDGE_CLIP_ERROR_UV_COORD);

// cellSizeToLongEdgeRatio defines the cell size relative to the length of an
// edge at which it is first considered to be long. Long edges do not
// contribute toward the decision to subdivide a cell further. For example,
// a value of 2.0 means that the cell must be at least twice the size of the
// edge in order for that edge to be counted. There are two reasons for not
// counting long edges: (1) such edges typically need to be propagated to
// several children, which increases time and memory costs without much benefit,
// and (2) in pathological cases, many long edges close together could force
// subdivision to continue all the way to the leaf cell level.
pub const CELL_SIZE_TO_LONG_EDGE_RATIO: f64 = 1.0;

// clippedShape represents the part of a shape that intersects a Cell.
// It consists of the set of edge IDs that intersect that cell and a boolean
// indicating whether the center of the cell is inside the shape (for shapes
// that have an interior).
//
// Note that the edges themselves are not clipped; we always use the original
// edges for intersection tests so that the results will be the same as the
// original shape.
#[derive(Debug, Clone)]
pub struct ClippedShape {
    // shapeID is the index of the shape this clipped shape is a part of.
    shape_id: i32,
    // containsCenter indicates if the center of the CellID this shape has been
    // clipped to falls inside this shape. This is false for shapes that do not
    // have an interior.
    contains_center: bool,

    // edges is the ordered set of ShapeIndex original edge IDs. Edges
    // are stored in increasing order of edge ID.
    edges: Vec<i32>
}

impl ClippedShape {
    // new returns a new clipped shape for the given shapeID and number of expected edges.
    pub fn new(id: i32, num_edges: usize) -> ClippedShape {
        ClippedShape {
            shape_id: id,
            contains_center: false,
            edges: Vec::with_capacity(num_edges),
        }
    }

    // num_edges returns the number of edges that intersect the CellID of the Cell this was clipped to.
    pub fn num_edges(&self) -> usize {
        self.edges.len()
    }

    // contains_edge reports if this clipped shape contains the given edge ID.
    pub fn contains_edge(&self, id: i32) -> bool {
        // Linear search is fast because the number of edges per shape is typically
        // very small (less than 10).
        self.edges.iter().any(|&e| e == id)
    }
}

// ShapeIndexCell stores the index contents for a particular CellID.
#[derive(Debug, Clone)]
pub struct ShapeIndexCell {
    shapes: Vec<ClippedShape>
}

impl ShapeIndexCell {
    // new creates a new cell that is sized to hold the given number of shapes.
    pub fn new(num_shapes: usize) -> ShapeIndexCell {
        ShapeIndexCell {
            shapes: Vec::with_capacity(num_shapes),
        }
    }

    // num_edges reports the total number of edges in all clipped shapes in this cell.
    pub fn num_edges(&self) -> usize {
        self.shapes.iter().map(|cs| cs.num_edges()).sum()
    }

    // add adds the given clipped shape to this index cell.
    pub fn add(&mut self, c: ClippedShape) {
        // C++ uses a set, so it's ordered and unique. We don't currently catch
        // the case when a duplicate value is added.
        self.shapes.push(c);
    }

    // find_by_shape_id returns the clipped shape that contains the given shapeID,
    // or None if none of the clipped shapes contain it.
    pub fn find_by_shape_id(&self, shape_id: i32) -> Option<&ClippedShape> {
        // Linear search is fine because the number of shapes per cell is typically
        // very small (most often 1), and is large only for pathological inputs
        // (e.g. very deeply nested loops).
        self.shapes.iter().find(|clipped| clipped.shape_id == shape_id)
    }
}

// faceEdge and clippedEdge store temporary edge data while the index is being
// updated.
//
// While it would be possible to combine all the edge information into one
// structure, there are two good reasons for separating it:
//
//  - Memory usage. Separating the two means that we only need to
//    store one copy of the per-face data no matter how many times an edge is
//    subdivided, and it also lets us delay computing bounding boxes until
//    they are needed for processing each face (when the dataset spans
//    multiple faces).
//
//  - Performance. UpdateEdges is significantly faster on large polygons when
//    the data is separated, because it often only needs to access the data in
//    clippedEdge and this data is cached more successfully.

// faceEdge represents an edge that has been projected onto a given face,
#[derive(Debug, Clone)]
pub struct FaceEdge {
    shape_id: i32,      // The ID of shape that this edge belongs to
    edge_id: i32,       // Edge ID within that shape
    max_level: i32,     // Not desirable to subdivide this edge beyond this level
    has_interior: bool, // Belongs to a shape that has a dimension of 2
    a: Point,         // The edge endpoints, clipped to a given face
    b: Point,
    edge: Edge,         // The original edge.
}

// clippedEdge represents the portion of that edge that has been clipped to a given Cell.
#[derive(Debug, Clone)]
pub struct ClippedEdge {
    face_edge: FaceEdge, // The original unclipped edge
    bound: R2Rect,       // Bounding box for the clipped portion
}

// ShapeIndexIteratorPos defines the set of possible iterator starting positions. By
// default iterators are unpositioned, since this avoids an extra seek in this
// situation where one of the seek methods (such as Locate) is immediately called.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ShapeIndexIteratorPos {
    // Begin specifies the iterator should be positioned at the beginning of the index.
    Begin,
    // End specifies the iterator should be positioned at the end of the index.
    End,
}

// `[ShapeIndexIterator]` is an iterator that provides low-level access to
// the cells of the index. Cells are returned in increasing order of CellID.
//
//	for it := index.Iterator(); !it.Done(); it.Next() {
//	  fmt.Print(it.CellID())
//	}
#[derive(Debug, Clone)]
pub struct ShapeIndexIterator<'a> {
    index: &'a ShapeIndex,
    position: usize,
    id: CellID,
    cell: Option<&'a ShapeIndexCell>,
}

impl<'a> Iterator for ShapeIndexIterator<'a> {
    type Item = &'a ShapeIndexCell;
    fn next(&mut self) -> Option<Self::Item> {
        let retv = self.index_cell();
        self.next();
        retv
    }
}

impl<'a> ShapeIndexIterator<'a> {
    // new creates a new iterator for the given index. If a starting
    // position is specified, the iterator is positioned at the given spot.
    pub fn new(index: &'a ShapeIndex, pos: Option<ShapeIndexIteratorPos>) -> Self {
        let mut s = ShapeIndexIterator {
            index,
            position: 0,
            id: CellID::sentinel(),
            cell: None,
        };

        if let Some(pos) = pos {
            match pos {
                ShapeIndexIteratorPos::Begin => s.begin(),
                ShapeIndexIteratorPos::End => s.end(),
            }
        }

        s
    }

    // clone returns a copy of this iterator.
    pub fn clone(&self) -> ShapeIndexIterator<'a> {
        ShapeIndexIterator {
            index: self.index,
            position: self.position,
            id: self.id,
            cell: self.cell,
        }
    }

    // cell_id returns the CellID of the current index cell.
    // If s.Done() is true, a value larger than any valid CellID is returned.
    pub fn cell_id(&self) -> CellID {
        self.id
    }

    // index_cell returns the current index cell.
    pub fn index_cell(&self) -> Option<&'a ShapeIndexCell> {
        self.cell
    }

    // center returns the Point at the center of the current position of the iterator.
    pub fn center(&self) -> Point {
        self.cell_id().center_point()
    }

    // begin positions the iterator at the beginning of the index.
    pub fn begin(&mut self) {
        if !self.index.is_fresh() {
            self.index.maybe_apply_updates();
        }
        self.position = 0;
        self.refresh();
    }

    // next positions the iterator at the next index cell.
    pub fn next(&mut self) {
        self.position += 1;
        self.refresh();
    }

    /// `[prev]` advances the iterator to the previous cell in the index and returns true to
    /// indicate it was not yet at the beginning of the index. If the iterator is at the
    /// first cell the call does nothing and returns false.
    pub fn prev(&mut self) -> bool {
        if self.position <= 0 {
            return false;
        }

        self.position -= 1;
        self.refresh();
        true
    }

    // end positions the iterator at the end of the index.
    pub fn end(&mut self) {
        self.position = self.index.cells.len();
        self.refresh();
    }

    // done reports if the iterator is positioned at or after the last index cell.
    pub fn done(&self) -> bool {
        self.id == CellID::sentinel()
    }

    // refresh updates the stored internal iterator values.
    fn refresh(&mut self) {
        if self.position < self.index.cells.len() {
            self.id = self.index.cells[self.position];
            self.cell = self.index.cell_map.get(&self.id);
        } else {
            self.id = CellID::sentinel();
            self.cell = None;
        }
    }

    // seek positions the iterator at the first cell whose ID >= target, or at the
    // end of the index if no such cell exists.
    pub fn seek(&mut self, target: CellID) {
        // Using binary search to find the position
        self.position = self.index.cells.binary_search(&target).unwrap_or_else(|pos| pos);
        self.refresh();
    }

    // locate_point positions the iterator at the cell that contains the given Point.
    // If no such cell exists, the iterator position is unspecified, and false is returned.
    // The cell at the matched position is guaranteed to contain all edges that might
    // intersect the line segment between target and the cell's center.
    pub fn locate_point(&mut self, p: Point) -> bool {
        // Let I = cellMap.LowerBound(T), where T is the leaf cell containing
        // point P. Then if T is contained by an index cell, then the
        // containing cell is either I or I'. We test for containment by comparing
        // the ranges of leaf cells spanned by T, I, and I'.
        let target = p.into();
        self.seek(target);
        if !self.done() && self.cell_id().range_min() <= target {
            return true;
        }

        if self.prev() && self.cell_id().range_max() >= target {
            return true;
        }
        false
    }

    // locate_cell_id attempts to position the iterator at the first matching index cell
    // in the index that has some relation to the given CellID. Let T be the target CellID.
    // If T is contained by (or equal to) some index cell I, then the iterator is positioned
    // at I and returns Indexed. Otherwise if T contains one or more (smaller) index cells,
    // then the iterator is positioned at the first such cell I and return Subdivided.
    // Otherwise Disjoint is returned and the iterator position is undefined.
    pub fn locate_cell_id(&mut self, target: CellID) -> CellRelation {
        // Let T be the target, let I = cellMap.LowerBound(T.RangeMin()), and
        // let I' be the predecessor of I. If T contains any index cells, then T
        // contains I. Similarly, if T is contained by an index cell, then the
        // containing cell is either I or I'. We test for containment by comparing
        // the ranges of leaf cells spanned by T, I, and I'.
        self.seek(target.range_min());
        if !self.done() {
            if self.cell_id() >= target && self.cell_id().range_min() <= target {
                return CellRelation::Indexed;
            }
            if self.cell_id() <= target.range_max() {
                return CellRelation::Subdivided;
            }
        }
        if self.prev() && self.cell_id().range_max() >= target {
            return CellRelation::Indexed;
        }
        CellRelation::Disjoint
    }
}


// tracker keeps track of which shapes in a given set contain a particular point
// (the focus). It provides an efficient way to move the focus from one point
// to another and incrementally update the set of shapes which contain it. We use
// this to compute which shapes contain the center of every CellID in the index,
// by advancing the focus from one cell center to the next.
//
// Initially the focus is at the start of the CellID space-filling curve. We then
// visit all the cells that are being added to the ShapeIndex in increasing order
// of CellID. For each cell, we draw two edges: one from the entry vertex to the
// center, and another from the center to the exit vertex (where entry and exit
// refer to the points where the space-filling curve enters and exits the cell).
// By counting edge crossings we can incrementally compute which shapes contain
// the cell center. Note that the same set of shapes will always contain the exit
// point of one cell and the entry point of the next cell in the index, because
// either (a) these two points are actually the same, or (b) the intervening
// cells in CellID order are all empty, and therefore there are no edge crossings
// if we follow this path from one cell to the other.
#[derive(Debug, Clone)]
pub struct Tracker {
    is_active: bool,
    a: Point,
    b: Point,
    next_cell_id: CellID,
    crosser: Option<EdgeCrosser>,
    shape_ids: Vec<i32>,

    // Shape ids saved by save_and_clear_state_before. The state is never saved
    // recursively so we don't need to worry about maintaining a stack.
    saved_ids: Vec<i32>,
}

impl Tracker {
    // new returns a new tracker with the appropriate defaults.
    pub fn new() -> Self {
        // As shapes are added, we compute which ones contain the start of the
        // CellID space-filling curve by drawing an edge from OriginPoint to this
        // point and counting how many shape edges cross this edge.
        let mut t = Tracker {
            is_active: false,
            b: Self::tracker_origin(),
            next_cell_id: CellID::from_face(0).child_begin_at_level(CellID::MAX_LEVEL),
            crosser: None,
            shape_ids: Vec::new(),
            saved_ids: Vec::new(),
        };

        // CellID curve start
        t.draw_to(Point::from_coords(
            -1.0 / std::f64::consts::SQRT_3,
            -1.0 / std::f64::consts::SQRT_3,
            -1.0 / std::f64::consts::SQRT_3,
        ));

        t
    }

    // tracker_origin returns the initial focus point when the tracker is created
    // (corresponding to the start of the CellID space-filling curve).
    fn tracker_origin() -> Point {
        // The start of the S2CellId space-filling curve.
        Point::from_coords(
            -1.0 / std::f64::consts::SQRT_3,
            -1.0 / std::f64::consts::SQRT_3,
            -1.0 / std::f64::consts::SQRT_3,
        )
    }

    // focus returns the current focus point of the tracker.
    pub fn focus(&self) -> Point {
        self.b
    }

    // add_shape adds a shape whose interior should be tracked. contains_focus indicates
    // whether the current focus point is inside the shape. Alternatively, if
    // the focus point is in the process of being moved (via moveTo/drawTo), you
    // can also specify contains_focus at the old focus point and call testEdge
    // for every edge of the shape that might cross the current drawTo line.
    // This updates the state to correspond to the new focus point.
    //
    // This requires shape.has_interior
    pub fn add_shape(&mut self, shape_id: i32, contains_focus: bool) {
        self.is_active = true;
        if contains_focus {
            self.toggle_shape(shape_id);
        }
    }

    // move_to moves the focus of the tracker to the given point. This method should
    // only be used when it is known that there are no edge crossings between the old
    // and new focus locations; otherwise use drawTo.
    pub fn move_to(&mut self, b: Point) {
        self.b = b;
    }

    // draw_to moves the focus of the tracker to the given point. After this method is
    // called, test_edge should be called with all edges that may cross the line
    // segment between the old and new focus locations.
    pub fn draw_to(&mut self, b: Point) {
        self.a = self.b;
        self.b = b;
        // TODO: the edge crosser may need an in-place Init method if this gets expensive
        self.crosser = Some(EdgeCrosser::new(self.a, self.b));
    }

    // test_edge checks if the given edge crosses the current edge, and if so, then
    // toggle the state of the given shapeID.
    // This requires shape to have an interior.
    pub fn test_edge(&mut self, shape_id: i32, edge: Edge) {
        if let Some(ref crosser) = self.crosser {
            if crosser.edge_or_vertex_crossing(edge.v0, edge.v1) {
                self.toggle_shape(shape_id);
            }
        }
    }

    // set_next_cell_id is used to indicate that the last argument to moveTo or drawTo
    // was the entry vertex of the given CellID, i.e. the tracker is positioned at the
    // start of this cell. By using this method together with atCellID, the caller
    // can avoid calling moveTo in cases where the exit vertex of the previous cell
    // is the same as the entry vertex of the current cell.
    pub fn set_next_cell_id(&mut self, next_cell_id: CellID) {
        self.next_cell_id = next_cell_id.range_min();
    }

    // at_cell_id reports if the focus is already at the entry vertex of the given
    // CellID (provided that the caller calls setNextCellID as each cell is processed).
    pub fn at_cell_id(&self, cell_id: CellID) -> bool {
        cell_id.range_min() == self.next_cell_id
    }

    // toggle_shape adds or removes the given shapeID from the set of IDs it is tracking.
    fn toggle_shape(&mut self, shape_id: i32) {
        // Most shapeIDs slices are small, so special case the common steps.

        // If there is nothing here, add it.
        if self.shape_ids.is_empty() {
            self.shape_ids.push(shape_id);
            return;
        }

        // If it's the first element, drop it from the slice.
        if self.shape_ids[0] == shape_id {
            self.shape_ids.remove(0);
            return;
        }

        // Binary search for the insertion position
        match self.shape_ids.binary_search(&shape_id) {
            // Found it, so remove it
            Ok(index) => {
                self.shape_ids.remove(index);
            }
            // Not found, so insert it at the right position
            Err(index) => {
                self.shape_ids.insert(index, shape_id);
            }
        }
    }

    // save_and_clear_state_before makes an internal copy of the state for shape ids below
    // the given limit, and then clear the state for those shapes. This is used during
    // incremental updates to track the state of added and removed shapes separately.
    pub fn save_and_clear_state_before(&mut self, limit_shape_id: i32) {
        let limit = self.lower_bound(limit_shape_id);
        self.saved_ids = self.shape_ids[..limit as usize].to_vec();
        self.shape_ids.drain(..limit as usize);
    }

    // restore_state_before restores the state previously saved by save_and_clear_state_before.
    // This only affects the state for shapeIDs below "limitShapeID".
    pub fn restore_state_before(&mut self, limit_shape_id: i32) {
        let limit = self.lower_bound(limit_shape_id);
        let mut new_ids = self.saved_ids.clone();
        new_ids.extend_from_slice(&self.shape_ids[limit as usize..]);
        self.shape_ids = new_ids;
        self.saved_ids.clear();
    }

    // lower_bound returns the index of the first entry x where x >= shapeID.
    fn lower_bound(&self, shape_id: i32) -> i32 {
        match self.shape_ids.binary_search(&shape_id) {
            Ok(index) => index as i32,
            Err(index) => index as i32,
        }
    }
}

Next, let's implement the RemovedShape struct:

// RemovedShape represents a set of edges from the given shape that is queued for removal.
#[derive(Debug, Clone)]
pub struct RemovedShape {
    shape_id: i32,
    has_interior: bool,
    contains_tracker_origin: bool,
    edges: Vec<Edge>,
}

// Constants for the ShapeIndex status
const STALE: i32 = 0;     // There are pending updates.
const UPDATING: i32 = 1;  // Updates are currently being applied.
const FRESH: i32 = 2;     // There are no pending updates.

Now let's start on the main ShapeIndex struct:

// ShapeIndex indexes a set of Shapes, where a Shape is some collection of edges
// that optionally defines an interior. It can be used to represent a set of
// points, a set of polylines, or a set of polygons. For Shapes that have
// interiors, the index makes it very fast to determine which Shape(s) contain
// a given point or region.
//
// The index can be updated incrementally by adding or removing shapes. It is
// designed to handle up to hundreds of millions of edges. All data structures
// are designed to be small, so the index is compact; generally it is smaller
// than the underlying data being indexed. The index is also fast to construct.
//
// Polygon, Loop, and Polyline implement Shape which allows these objects to
// be indexed easily. You can find useful query methods in CrossingEdgeQuery
// and ClosestEdgeQuery (Not yet implemented in Go).
//
// Example showing how to build an index of Polylines:
//
//	index := NewShapeIndex()
//	for _, polyline := range polylines {
//	    index.Add(polyline);
//	}
//	// Now you can use a CrossingEdgeQuery or ClosestEdgeQuery here.
#[derive(Debug)]
pub struct ShapeIndex {
    // shapes is a map of shape ID to shape.
    shapes: BTreeMap<i32, Box<dyn Shape>>,

    // The maximum number of edges per cell.
    // TODO(roberts): Update the comments when the usage of this is implemented.
    max_edges_per_cell: i32,

    // nextID tracks the next ID to hand out. IDs are not reused when shapes
    // are removed from the index.
    next_id: i32,

    // cellMap is a map from CellID to the set of clipped shapes that intersect that
    // cell. The cell IDs cover a set of non-overlapping regions on the sphere.
    // In C++, this is a BTree, so the cells are ordered naturally by the data structure.
    cell_map: BTreeMap<CellID, ShapeIndexCell>,
    // Track the ordered list of cell IDs.
    cells: Vec<CellID>,

    // The current status of the index; accessed atomically.
    status: AtomicI32,

    // Additions and removals are queued and processed on the first subsequent
    // query. There are several reasons to do this:
    //
    //  - It is significantly more efficient to process updates in batches if
    //    the amount of entities added grows.
    //  - Often the index will never be queried, in which case we can save both
    //    the time and memory required to build it. Examples:
    //     + Loops that are created simply to pass to an Polygon. (We don't
    //       need the Loop index, because Polygon builds its own index.)
    //     + Applications that load a database of geometry and then query only
    //       a small fraction of it.
    //
    // The main drawback is that we need to go to some extra work to ensure that
    // some methods are still thread-safe. Note that the goal is *not* to
    // make this thread-safe in general, but simply to hide the fact that
    // we defer some of the indexing work until query time.
    //
    // This mutex protects all of following fields in the index.
    mu: Mutex<()>,

    // pendingAdditionsPos is the index of the first entry that has not been processed
    // via applyUpdatesInternal.
    pending_additions_pos: i32,

    // The set of shapes that have been queued for removal but not processed yet by
    // applyUpdatesInternal.
    pending_removals: Vec<RemovedShape>,
}

impl ShapeIndex {
    // new creates a new ShapeIndex.
    pub fn new() -> Self {
        ShapeIndex {
            max_edges_per_cell: 10,
            shapes: BTreeMap::new(),
            cell_map: BTreeMap::new(),
            cells: Vec::new(),
            status: AtomicI32::new(FRESH),
            next_id: 0,
            mu: Mutex::new(()),
            pending_additions_pos: 0,
            pending_removals: Vec::new(),
        }
    }

    // iterator returns an iterator for this index.
    pub fn iterator(&self) -> ShapeIndexIterator {
        self.maybe_apply_updates();
        ShapeIndexIterator::new(self, Some(ShapeIndexIteratorPos::Begin))
    }

    // begin positions the iterator at the first cell in the index.
    pub fn begin(&self) -> ShapeIndexIterator {
        self.maybe_apply_updates();
        ShapeIndexIterator::new(self, Some(ShapeIndexIteratorPos::Begin))
    }

    // end positions the iterator at the last cell in the index.
    pub fn end(&self) -> ShapeIndexIterator {
        // TODO(roberts): It's possible that updates could happen to the index between
        // the time this is called and the time the iterators position is used and this
        // will be invalid or not the end. For now, things will be undefined if this
        // happens. See about referencing the IsFresh to guard for this in the future.
        self.maybe_apply_updates();
        ShapeIndexIterator::new(self, Some(ShapeIndexIteratorPos::End))
    }

    // region returns a new ShapeIndexRegion for this ShapeIndex.
    pub fn region(&self) -> ShapeIndexRegion {
        ShapeIndexRegion {
            index: self,
            contains_query: ContainsPointQuery::new(self, VertexModel::SemiOpen),
            iter: self.iterator(),
        }
    }

    // len reports the number of Shapes in this index.
    pub fn len(&self) -> usize {
        self.shapes.len()
    }

    // is_empty reports whether this index is empty (has no shapes).
    pub fn is_empty(&self) -> bool {
        self.shapes.is_empty()
    }

    // reset resets the index to its original state.
    pub fn reset(&mut self) {
        self.shapes.clear();
        self.next_id = 0;
        self.cell_map.clear();
        self.cells.clear();
        self.status.store(FRESH, Ordering::SeqCst);
    }

    // num_edges returns the number of edges in this index.
    pub fn num_edges(&self) -> usize {
        self.shapes.values().map(|shape| shape.num_edges()).sum()
    }

    // num_edges_up_to returns the number of edges in the given index, up to the given
    // limit. If the limit is encountered, the current running total is returned,
    // which may be more than the limit.
    pub fn num_edges_up_to(&self, limit: usize) -> usize {
        let mut num_edges = 0;
        // We choose to iterate over the shapes in order to match the counting
        // up behavior in C++ and for test compatibility instead of using a
        // more idiomatic range over the shape map.
        for i in 0..=self.next_id {
            if let Some(s) = self.shape(i) {
                num_edges += s.num_edges();
                if num_edges >= limit {
                    break;
                }
            }
        }

        num_edges
    }

    // shape returns the shape with the given ID, or None if the shape has been removed from the index.
    pub fn shape(&self, id: i32) -> Option<&dyn Shape> {
        self.shapes.get(&id).map(|s| s.as_ref())
    }

    // id_for_shape returns the id of the given shape in this index, or -1 if it is
    // not in the index.
    //
    // TODO(roberts): Need to figure out an appropriate way to expose this on a Shape.
    // C++ allows a given S2 type (Loop, Polygon, etc) to be part of multiple indexes.
    // By having each type extend S2Shape which has an id element, they all inherit their
    // own id field rather than having to track it themselves.
    pub fn id_for_shape(&self, shape: &dyn Shape) -> i32 {
        for (k, v) in &self.shapes {
            if std::ptr::eq(v.as_ref() as *const dyn Shape, shape as *const dyn Shape) {
                return *k;
            }
        }
        -1
    }

    // add adds the given shape to the index and returns the assigned ID.
    pub fn add(&mut self, shape: Box<dyn Shape>) -> i32 {
        let id = self.next_id;
        self.shapes.insert(id, shape);
        self.next_id += 1;
        self.status.store(STALE, Ordering::SeqCst);
        id
    }

    // remove removes the given shape from the index.
    pub fn remove(&mut self, shape: &dyn Shape) {
        // The index updates itself lazily because it is much more efficient to
        // process additions and removals in batches.
        let id = self.id_for_shape(shape);

        // If the shape wasn't found, it's already been removed or was not in the index.
        if !self.shapes.contains_key(&id) {
            return;
        }

        // Remove the shape from the shapes map.
        self.shapes.remove(&id);

        // We are removing a shape that has not yet been added to the index,
        // so there is nothing else to do.
        if id >= self.pending_additions_pos {
            return;
        }

        let shape = match shape.as_any().downcast_ref::<Shape>() {
            Some(s) => s,
            None => return,
        };

        let num_edges = shape.num_edges();
        let removed = RemovedShape {
            shape_id: id,
            has_interior: shape.dimension() == 2,
            contains_tracker_origin: shape.reference_point().contained,
            edges: (0..num_edges).map(|e| shape.edge(e)).collect(),
        };

        self.pending_removals.push(removed);
        self.status.store(STALE, Ordering::SeqCst);
    }

    // build triggers the update of the index. Calls to Add and Release are normally
    // queued and processed on the first subsequent query. This has many advantages,
    // the most important of which is that sometimes there *is* no subsequent
    // query, which lets us avoid building the index completely.
    //
    // This method forces any pending updates to be applied immediately.
    pub fn build(&self) {
        self.maybe_apply_updates();
    }

    // is_fresh reports if there are no pending updates that need to be applied.
    // This can be useful to avoid building the index unnecessarily, or for
    // choosing between two different algorithms depending on whether the index
    // is available.
    //
    // The returned index status may be slightly out of date if the index was
    // built in a different thread. This is fine for the intended use (as an
    // efficiency hint), but it should not be used by internal methods.
    pub fn is_fresh(&self) -> bool {
        self.status.load(Ordering::SeqCst) == FRESH
    }

    // is_first_update reports if this is the first update to the index.
    fn is_first_update(&self) -> bool {
        // Note that it is not sufficient to check whether cellMap is empty, since
        // entries are added to it during the update process.
        self.pending_additions_pos == 0
    }

    // is_shape_being_removed reports if the shape with the given ID is currently slated for removal.
    fn is_shape_being_removed(&self, shape_id: i32) -> bool {
        // All shape ids being removed fall below the index position of shapes being added.
        shape_id < self.pending_additions_pos
    }

    // maybe_apply_updates checks if the index pieces have changed, and if so, applies pending updates.
    fn maybe_apply_updates(&self) {
        // TODO(roberts): To avoid acquiring and releasing the mutex on every
        // query, we should use atomic operations when testing whether the status
        // is fresh and when updating the status to be fresh. This guarantees
        // that any thread that sees a status of fresh will also see the
        // corresponding index updates.
        if self.status.load(Ordering::SeqCst) != FRESH {
            let _lock = self.mu.lock().unwrap();
            self.apply_updates_internal();
            self.status.store(FRESH, Ordering::SeqCst);
        }
    }

    // apply_updates_internal does the actual work of updating the index by applying all
    // pending additions and removals. It does *not* update the indexes status.
    fn apply_updates_internal(&self) {
        // TODO(roberts): Building the index can use up to 20x as much memory per
        // edge as the final index memory size. If this causes issues, add in
        // batched updating to limit the amount of items per batch to a
        // configurable memory footprint overhead.
        let t = Tracker::new();

        // allEdges maps a Face to a collection of faceEdges.
        let mut all_edges: Vec<Vec<FaceEdge>> = vec![Vec::new(); 6];

        for p in &self.pending_removals {
            self.remove_shape_internal(p, &mut all_edges, &mut t);
        }

        for id in self.pending_additions_pos..self.next_id {
            self.add_shape_internal(id, &mut all_edges, &mut t);
        }

        for face in 0..6 {
            self.update_face_edges(face, &all_edges[face], &mut t);
        }

        self.pending_removals.clear();
        self.pending_additions_pos = self.next_id;
        // It is the caller's responsibility to update the index status.
    }

    // add_shape_internal clips all edges of the given shape to the six cube faces,
    // adds the clipped edges to the set of allEdges, and starts tracking its
    // interior if necessary.
    fn add_shape_internal(&self, shape_id: i32, all_edges: &mut [Vec<FaceEdge>], t: &mut Tracker) {
        let shape = match self.shapes.get(&shape_id) {
            Some(s) => s.as_ref(),
            None => return, // This shape has already been removed.
        };

        let face_edge = FaceEdge {
            shape_id,
            edge_id: 0,
            max_level: 0,
            has_interior: shape.dimension() == 2,
            a: R2Point::new(0.0, 0.0),
            b: R2Point::new(0.0, 0.0),
            edge: Edge::default(),
        };

        if face_edge.has_interior {
            t.add_shape(shape_id, contains_brute_force(shape, t.focus()));
        }

        let num_edges = shape.num_edges();
        for e in 0..num_edges {
            let edge = shape.edge(e);

            let mut fe = face_edge.clone();
            fe.edge_id = e as i32;
            fe.edge = edge;
            fe.max_level = max_level_for_edge(edge);
            self.add_face_edge(fe, all_edges);
        }
    }

    // add_face_edge adds the given faceEdge into the collection of all edges.
    fn add_face_edge(&self, fe: FaceEdge, all_edges: &mut [Vec<FaceEdge>]) {
        let a_face = face(fe.edge.v0.vector());
        // See if both endpoints are on the same face, and are far enough from
        // the edge of the face that they don't intersect any (padded) adjacent face.
        if a_face == face(fe.edge.v1.vector()) {
            let (x, y) = valid_face_xyz_to_uv(a_face, fe.edge.v0.vector());
            let mut fe = fe.clone();
            fe.a = R2Point::new(x, y);

            let (x, y) = valid_face_xyz_to_uv(a_face, fe.edge.v1.vector());
            fe.b = R2Point::new(x, y);

            let max_uv = 1.0 - CELL_PADDING;
            if fe.a.x().abs() <= max_uv && fe.a.y().abs() <= max_uv &&
                fe.b.x().abs() <= max_uv && fe.b.y().abs() <= max_uv {
                all_edges[a_face as usize].push(fe);
                return;
            }
        }

        // Otherwise, we simply clip the edge to all six faces.
        for face in 0..6 {
            if let Some((a_clip, b_clip)) = clip_to_padded_face(fe.edge.v0, fe.edge.v1, face, CELL_PADDING) {
                let mut fe = fe.clone();
                fe.a = a_clip;
                fe.b = b_clip;
                all_edges[face as usize].push(fe);
            }
        }
    }

    // TODO: Implement the remaining methods of ShapeIndex
}
