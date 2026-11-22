import ProximityPrize.SubmissionLower.ListProofA
import ProximityPrize.SubmissionLower.CurveListScalarWide55Defs -- serialize candidate build

namespace CurveListJointWeight

/-- In order two this reads the exponent of f' plus three times the exponent of f''. -/
def weight {n : ℕ} (j : Fin n) : ℕ := 2*j.val-1

def jetWeight (n : ℕ) : Option (Fin n) → ℕ := fun j => j.elim 0 weight

end CurveListJointWeight
