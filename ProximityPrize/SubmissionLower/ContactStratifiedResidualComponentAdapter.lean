import ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapter
import ProximityPrize.SubmissionLower.ContactNearPencil6600Arithmetic
namespace ProximityPrize.SubmissionLower.ContactStratifiedResidualComponentAdapter

open scoped Classical BigOperators
open ActualCurveCoordinateField ActualCurveZeroCount
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount ContactComponentPencils
open ContactResidualSparseComponentAdapter

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable (phi : Polynomial K →+* Omega)
variable {Iota : Type*}

omit [IsAlgClosed Omega] in
theorem aggregate_component_stratified_incidence
    (G T H : MvPolynomial (Fin 3) Omega)
    {Seed : Type*} (S : Finset Seed) (v : Seed → Fin 3 → Omega)
    (hG : ∀ gamma ∈ S, MvPolynomial.eval (v gamma) G = 0)
    (hT : ∀ gamma ∈ S, MvPolynomial.eval (v gamma) T = 0)
    (hH : ∀ gamma ∈ S, MvPolynomial.eval (v gamma) H ≠ 0)
    (gap U V pencil degreeWhole unitWhole zBudget : ℕ)
    (degreeCost unitCost zDegree : RegularComponent Omega G T H → ℕ)
    (hcomponent : ∀ C,
      (componentSeeds Omega G T H S v C).card * gap ≤
        U * degreeCost C + V * unitCost C +
          pencil * gap * zDegree C)
    (hdegree : (∑ C, degreeCost C) ≤ degreeWhole)
    (hunit : (∑ C, unitCost C) ≤ unitWhole)
    (hz : (∑ C, zDegree C) ≤ zBudget) :
    S.card * gap ≤
      U * degreeWhole + V * unitWhole + pencil * gap * zBudget := by
  classical
  calc
    S.card * gap ≤
        (∑ C : RegularComponent Omega G T H,
          (componentSeeds Omega G T H S v C).card) * gap :=
      Nat.mul_le_mul_right gap
        (card_le_sum_componentSeeds Omega G T H S v hG hT hH)
    _ = ∑ C : RegularComponent Omega G T H,
        (componentSeeds Omega G T H S v C).card * gap := by
      rw [Finset.sum_mul]
    _ ≤ ∑ C : RegularComponent Omega G T H,
        (U * degreeCost C + V * unitCost C + pencil * gap * zDegree C) :=
      Finset.sum_le_sum (fun C _ ↦ hcomponent C)
    _ = U * (∑ C : RegularComponent Omega G T H, degreeCost C) +
        V * (∑ C : RegularComponent Omega G T H, unitCost C) +
        pencil * gap *
          (∑ C : RegularComponent Omega G T H, zDegree C) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ U * degreeWhole + V * unitWhole + pencil * gap * zBudget :=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left U hdegree)
          (Nat.mul_le_mul_left V hunit))
        (Nat.mul_le_mul_left (pencil * gap) hz)

end

end ProximityPrize.SubmissionLower.ContactStratifiedResidualComponentAdapter
