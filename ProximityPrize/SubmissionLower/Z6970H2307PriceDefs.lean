import ProximityPrize.SubmissionLower.Z6969Pack0836
import ProximityPrize.SubmissionLower.Low48BentSupport

set_option Elab.async false

namespace Low6969GeometryCut
open K1_13 (Shape chart mixed32 ceilDiv)
open Low6969Prices (primaryBox taylorLength)

def auxCurves32 (x : Shape) : ℕ :=
  let p := x.chamber
  let h := chart taylorLength p
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) h + 2 * x.t * mixed32 p p p h
def auxPoints32 (x : Shape) : ℕ :=
  let p := x.chamber
  mixed32 p primaryBox (primaryBox.plus (p.scale 4)) p + 2 * x.t * mixed32 p p p p
def membershipDegree (x : Shape) : ℕ :=
  x.b * primaryBox.b * (chart (taylorLength + 1) x.chamber).b
def chargedPrice (x : Shape) (l scale budget : ℕ) : ℕ :=
  ceilDiv (ceilDiv budget scale +
    ceilDiv ((82414 + 2 * 46352) * membershipDegree x) 46352) l +
  2 * (133378 * x.b * primaryBox.b) +
  ceilDiv (82414 * auxCurves32 x + 2 * 46352 * auxPoints32 x) (32 * 46352)

end Low6969GeometryCut

namespace Low6969RetainedCut
open K1_13 (Row Shape shape InBox mixed32 chart)
open Low6969Prices (primaryBox taylorLength tiltedFits tiltedSurface physicalPrice)
open Low6969GeometryCut (chargedPrice)

def residualBox (h : Shape) (l : ℕ) : Shape :=
  ⟨primaryBox.b-l*h.b, primaryBox.j-l*h.j, primaryBox.t-l*h.t⟩
/-- The accepted physical charge with an arbitrary mixed surface budget. -/
def cutPrice (x : Shape) (l scale surface : ℕ) := chargedPrice x l scale surface

def fourSurface (p q : Shape) :=
  mixed32 p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

def chamberHull (x : Shape) : Shape := ⟨max x.b x.j,x.j,min x.t (x.j/3)⟩

theorem hull_includes {Q : Row 4} {x : Shape} (hb : InBox (shape Q) x) :
    InBox (shape Q) (chamberHull x) := by
  have h := (K1_13_7_1.shape_chamber Q).2
  change 3*(shape Q).t ≤ (shape Q).j at h
  exact ⟨hb.1.trans (le_max_left _ _),hb.2.1, le_min hb.2.2 (by have := hb.2.1; omega)⟩

theorem hull_valid (x : Shape) : Low48BentLattice.Chamber (chamberHull x,0) := by
  refine ⟨le_max_right _ _,?_,Nat.zero_le _⟩
  change 3*min x.t (x.j/3) ≤ x.j
  have := min_le_right x.t (x.j/3)
  omega

def contractedPrice (x h : Shape) (l active : ℕ) : ℕ :=
  let q := chamberHull (residualBox h l)
  let old := physicalPrice x l active
  let four := if 0 < q.t then min old (cutPrice x l 32 (fourSurface x.chamber q)) else old
  if tiltedFits x then min four (cutPrice x l (60*32) (tiltedSurface x.chamber q)) else four

end Low6969RetainedCut

namespace Height2307Count6970
open K1_13 (Shape)
open Low6969SharedPrice (additiveBase)

def gatePrice (G : Shape → ℕ) (x : Shape) (l : ℕ) : ℕ :=
  additiveBase x l + Low6969SharedThirdCut.preciseFee x l + G x

end Height2307Count6970
