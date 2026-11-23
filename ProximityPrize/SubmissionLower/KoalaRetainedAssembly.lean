import ProximityPrize.SubmissionLower.KoalaRetainedWitness
import ProximityPrize.SubmissionLower.KoalaRetainedGeometry

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
namespace KoalaRetainedCut
noncomputable section

open P3 (I K)
open K1_13 (Geom Row Shape shape InBox OrderAt atJet extend)
open Final50Price (primaryBox primaryCutoff TrueWeightLE ActiveFits SmallFactor Messages
  tiltedFits tiltedSurface physicalPrice ProperCut)
open scoped Polynomial BigOperators

def chamberHull (x : Shape) : Shape := ⟨max x.b x.j,x.j,min x.t (x.j/3)⟩



def contractedPrice (x h : Shape) (l active : ℕ) : ℕ :=
  let q := chamberHull (residualBox h l)
  let old := physicalPrice x l active
  let four := if 0 < q.t then min old (cutPrice x l 32 (fourSurface x.chamber q)) else old
  if tiltedFits x then min four (cutPrice x l (60*32) (tiltedSurface x.chamber q)) else four




end
end KoalaRetainedCut
