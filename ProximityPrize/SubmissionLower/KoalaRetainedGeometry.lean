import ProximityPrize.SubmissionLower.Shared50BentCaps
import ProximityPrize.SubmissionLower.Shared50Tally

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

namespace KoalaRetainedCut
noncomputable section

open P3 (K I)
open K1_13 (Row Shape InBox shape mixed32 chart)
open Final50Price (Messages tiltedFits tiltedSurface taylorLength)
open Final50GeometryCut (CutInput )
open Final50GeometryCut (chargedPrice)
open scoped Polynomial BigOperators

/-- The accepted physical charge with an arbitrary mixed surface budget. -/
def cutPrice (x : Shape) (l scale surface : ℕ) := chargedPrice x l scale surface

def fourSurface (p q : Shape) :=
  mixed32 p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

variable {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}




end
end KoalaRetainedCut
