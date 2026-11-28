import ProximityPrize.SubmissionLower.Z6970H2307PointRows

set_option autoImplicit false

namespace Height2307PointCertificates
open Height2307Bands (Band)
open Height2307PointRowsCore (beginWidth covers endWidth)

inductive Segment where
  | tile (value : Tile)
  | gateRun (first last order bucket : Nat)

def Segment.tiles : Segment → List Tile
  | .tile value => [value]
  | .gateRun first last order bucket =>
    (List.range (last + 1 - first)).map fun i =>
      ⟨first + i, first + i, order, .gate, none, bucket⟩

structure RowData where
  t : Nat
  j : Nat
  segments : List Segment

def RowData.tiles (r : RowData) : List Tile := r.segments.flatMap Segment.tiles

def RowData.check (k : Band) (r : RowData) : Bool :=
  covers (endWidth k) (beginWidth r.j r.t) r.tiles && r.tiles.all (paid k r.j r.t)

def RowData.toRow {k : Band} (r : RowData) (h : r.check k = true) : Row k :=
  ⟨r.t, r.j, r.tiles, (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩

def checkedRows {k : Band} (rs : List RowData) (h : rs.all (RowData.check k) = true) :
    List (Row k) :=
  rs.attach.map fun r => r.1.toRow (List.all_eq_true.mp h r.1 r.2)

end Height2307PointCertificates
