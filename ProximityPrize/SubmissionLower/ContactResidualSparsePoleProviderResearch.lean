import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSparsePoleZeroCountResearch
import ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapterResearch

/-! .











 -/

namespace ProximityPrize.SubmissionLower.ContactResidualSparsePoleProviderResearch

open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField ActualCurveZeroCount
open ContactRegularComponentCover ContactProperCutSeedCount
open ContactSparsePoleSupportResearch ContactSparsePoleZeroCountResearch
open ContactResidualSparseComponentAdapterResearch
open CoordinateBoxZeroCount

noncomputable section

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

/-- .

 -/
structure ResidualPoleComponentBudget
    (G T H : MvPolynomial (Fin 3) Ω)
    (E : Finset (Fin 3 →₀ ℕ)) (separator : Fin 3) (wholeCost : ℕ) where
  cost : RegularComponent Ω G T H → ℕ
  separator_transcendental : ∀ C : RegularComponent Ω G T H,
    Transcendental Ω (coordinate Ω C.1 separator)
  pole_le : ∀ C : RegularComponent Ω G T H,
    let htr := separator_transcendental C
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C.1) :=
      ActualCurveRationalProjection.rationalBaseAlgebra Ω C.1 separator htr
    ∀ W : Finset (Place Ω (CoordinateField Ω C.1)),
      (∑ v ∈ W, exponentSetPoleWeight v.val (coordinate Ω C.1) E) ≤
        (cost C : ℤ)
  sum_cost_le : (∑ C : RegularComponent Ω G T H, cost C) ≤ wholeCost

/-- .
 -/
def ResidualPoleComponentBudget.toResidualComponentBudget
    {G T H : MvPolynomial (Fin 3) Ω}
    {E : Finset (Fin 3 →₀ ℕ)} {separator : Fin 3} {wholeCost : ℕ}
    (B : ResidualPoleComponentBudget G T H E separator wholeCost)
    (hproj : ∀ C : RegularComponent Ω G T H,
      ProjectionsFiniteSeparable Ω C.1) :
    ResidualComponentBudget G T H (fun A ↦ A.support ⊆ E) wholeCost where
  cost := B.cost
  zero_le := by
    intro C A hAE hproper points hpointsP hpointsA
    exact finite_zero_points_le_exponentSet_of_separator C.1 (hproj C)
      separator (B.separator_transcendental C) E (B.cost C) (B.pole_le C)
      A hAE hproper points hpointsP hpointsA
  sum_cost_le := B.sum_cost_le

end

end ProximityPrize.SubmissionLower.ContactResidualSparsePoleProviderResearch
