import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition

/-! Actual selected regular-factor families for the score-66.30 join. -/

namespace ProximityPrize.SubmissionLower.ContactRegularSeeds6630Research

open ContactRegularFactorFlag6630Research
open ContactPrimeSeedIncidence
open ContactSelectedSeedDecomposition

set_option autoImplicit false

noncomputable section

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

def regularSeeds6630 (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : RegularIndex Q) : Finset K := by
  classical
  exact Gamma.filter (fun gamma ↦ RegularSolution F.1 (selected gamma) gamma)

theorem regularSeeds6630_subset (Q : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (F : RegularIndex Q) :
    regularSeeds6630 Q selected Gamma F ⊆ Gamma :=
  by
    classical
    exact Finset.filter_subset _ _

end

end ProximityPrize.SubmissionLower.ContactRegularSeeds6630Research
