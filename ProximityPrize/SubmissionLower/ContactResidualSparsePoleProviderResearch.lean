import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSparsePoleZeroCountResearch
import ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapterResearch

/-!
# Tropical pole budget to residual sparse component provider

This is the final formal bridge before the global mixed-volume theorem.  A
single common separating coordinate is used on every retained component.  A
component cost is its Newton-support pole degree, and the costs are required
to sum to the target mixed volume.

The generic-shear argument supplies the common separator in the intended
application.  The still-missing geometric theorem is precisely `pole_le` plus
`sum_cost_le`; no affine zero-count, identity-component removal, or incidence
argument remains after this module.
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

/-- Componentwise tropical data for one fixed exponent set and one common
separating coordinate.  In the target application `wholeCost` is the exact
mixed volume `MV(Newt(G), Newt(T), E)`. -/
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

/-- The tropical component data constructs exactly the residual provider used
by the sharp incidence adapter. -/
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
