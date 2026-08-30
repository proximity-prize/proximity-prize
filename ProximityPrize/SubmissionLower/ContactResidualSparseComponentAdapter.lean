import ProximityPrize.SubmissionLower.ContactProperCutSeedCount

namespace ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapter

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveZeroCount
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils

noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable (φ : Polynomial K →+* Ω)

def FiniteZeroSetBound
    (P : Ideal (MvPolynomial (Fin 3) Ω))
    (A : MvPolynomial (Fin 3) Ω) (cost : ℕ) : Prop :=
  ∀ points : Finset (Fin 3 → Ω),
    (∀ v ∈ points, P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom) →
    (∀ v ∈ points, MvPolynomial.aeval v A = 0) →
    points.card ≤ cost

end

end ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapter
