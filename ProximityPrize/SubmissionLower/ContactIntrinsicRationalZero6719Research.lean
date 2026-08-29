import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRationalRegularZero6676Research
import ProximityPrize.SubmissionLower.ContactFieldPlaceTransport6719Research

/-! .
 -/

namespace ProximityPrize.SubmissionLower.ContactIntrinsicRationalZero6719Research

open scoped Classical BigOperators
open ActualCurveCoordinateField CoordinateBoxZeroCount
open ContactRegularZeroBudget6676Research ContactRationalRegularZero6676Research
open ContactWeakSeparableSeparatorResearch ContactFieldPlaceTransport6719Research
open ContactFlagAffineResidualAutomorphismResearch

noncomputable section

variable {K : Type} [Field K] [IsAlgClosed K]
local notation "Poly" => MvPolynomial (Fin 3) K

/-- . -/
def RationalZeroCriterion (P : Ideal Poly) [P.IsPrime] : Prop :=
  ∀ (H A : Poly) (k cost : ℕ), A ∉ P → H ∉ P →
    (∀ S : Finset (Place K (CoordinateField K P)),
      (∑ v ∈ S, CoordinatePoleMass.poleOrder K (CoordinateField K P) v
        (coordinateEvaluation K P A / (coordinateEvaluation K P H) ^ k)) ≤ (cost : ℤ)) →
    FiniteRegularZeroSetBound P H A cost

theorem RationalZeroCriterion.of_separator
    (P : Ideal Poly) [P.IsPrime] (base : SeparableLiteralCoordinate P) :
    RationalZeroCriterion P := by
  intro H A k cost hA hH hpole
  apply finite_regular_zero_bound_of_separator K P base H A k cost hA hH
  simpa only [coordinateEvaluation_eq_aeval] using hpole

/-- .
 -/
theorem RationalZeroCriterion.map_residual
    (P Q : Ideal Poly) [P.IsPrime] [Q.IsPrime]
    (h : RationalZeroCriterion P)
    (aY v bY aS bS cS : K) (hv : v ≠ 0)
    (hQ : Q = P.map (residualEquiv aY v bY aS bS cS hv).toRingHom) :
    RationalZeroCriterion Q := by
  intro H A k cost hA hH hpole
  let e := residualEquiv aY v bY aS bS cS hv
  let f := coordinateFieldEquiv P Q e hQ
  let oldA : Poly := e.symm A
  let oldH : Poly := e.symm H
  have hnot (T : Poly) (hT : T ∉ Q) : e.symm T ∉ P := by
    intro ht
    have hm := Ideal.mem_map_of_mem e.toRingHom ht
    change e (e.symm T) ∈ P.map e.toRingHom at hm
    rw [e.apply_symm_apply, ← hQ] at hm
    exact hT hm
  have hfield (T : Poly) :
      f (coordinateEvaluation K P (e.symm T)) = coordinateEvaluation K Q T := by
    dsimp only [f]
    rw [coordinateFieldEquiv_eval, e.apply_symm_apply]
  let oldValue := coordinateEvaluation K P oldA / (coordinateEvaluation K P oldH) ^ k
  let newValue := coordinateEvaluation K Q A / (coordinateEvaluation K Q H) ^ k
  have hvalue : f oldValue = newValue := by
    dsimp only [oldValue, newValue, oldA, oldH]
    rw [map_div₀, map_pow, hfield, hfield]
  have holdPole : ∀ S : Finset (Place K (CoordinateField K P)),
      (∑ w ∈ S, CoordinatePoleMass.poleOrder K (CoordinateField K P) w oldValue) ≤
        (cost : ℤ) := by
    have ht := finite_pole_bound_transport f.symm newValue cost hpole
    simpa only [← hvalue, f.symm_apply_apply] using ht
  have hz := h oldH oldA k cost (hnot A hA) (hnot H hH) holdPole
  change FiniteRegularZeroSetBound P
    (originalAlgHom aY v bY aS bS cS H)
    (originalAlgHom aY v bY aS bS cS A) cost at hz
  rw [hQ]
  exact hz.map_residual_of_inverse aY v bY aS bS cS hv

end

end ProximityPrize.SubmissionLower.ContactIntrinsicRationalZero6719Research
