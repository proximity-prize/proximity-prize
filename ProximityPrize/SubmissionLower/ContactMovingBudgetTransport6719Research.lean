import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactMovingCurveBudget6719Research
import ProximityPrize.SubmissionLower.ContactFieldPlaceTransport6719Research
import ProximityPrize.SubmissionLower.ContactMovingPoleTransport6719Research

/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactMovingBudgetTransport6719Research
open scoped Classical BigOperators WithZero
open ActualCurveCoordinateField CoordinateBoxZeroCount ContactLocalPoleBound
open ContactSparsePoleSupportResearch ContactFlagBezout6543Research
open ContactFlagPoleInequality6543Research ContactMovingProjection6676Research
open ContactFlagAffineResidualAutomorphismResearch ContactIdentityResidualPrimeTransportResearch
open ContactFieldPlaceTransport6719Research ContactMovingPoleTransport6719Research
open ContactCommonProjectionChoice6676Research ContactMovingCurveBudget6719Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

variable {K : Type} [Field K]
variable (P Q : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime] [Q.IsPrime]
variable (aY v bY aS bS cS : K) (hv : v ≠ 0)
variable (hQ : Q=P.map (residualEquiv aY v bY aS bS cS hv).toRingHom)
local notation "e" => residualEquiv aY v bY aS bS cS hv
local notation "Ψ" => coordinateFieldEquiv P Q e hQ

theorem residual_unit_weights (ν : Place K (CoordinateField K Q)) :
    exponentSetPoleWeight (placeComap Ψ ν).val (coordinate K P) (flagSupport unitZFlag)=
      exponentSetPoleWeight ν.val (coordinate K Q) (flagSupport unitZFlag) ∧
    exponentSetPoleWeight (placeComap Ψ ν).val (coordinate K P) (flagSupport unitYZFlag)=
      exponentSetPoleWeight ν.val (coordinate K Q) (flagSupport unitYZFlag) ∧
    exponentSetPoleWeight (placeComap Ψ ν).val (coordinate K P) (flagSupport unitAllFlag)=
      exponentSetPoleWeight ν.val (coordinate K Q) (flagSupport unitAllFlag) := by
  have hx : (fun i ↦ Ψ (coordinate K P i))=forward aY v bY aS bS cS (coordinate K Q) := by
    funext i
    exact coordinateFieldEquiv_residual_coordinate P Q aY v bY aS bS cS hv hQ i
  have h := unit_flag_poles_invariant ν.val (constant_value_le_one K (CoordinateField K Q) ν)
    aY v bY aS bS cS hv (coordinate K Q)
  rw [← hx] at h
  exact h

include hQ in
theorem residual_denominator_ne_zero (H H' : MvPolynomial (Fin 3) K) (t : K)
    (ht : t ≠ 0) (hH : H ∉ P) (hH' : H'=MvPolynomial.C t*e H) :
    coordinateEvaluation K Q H' ≠ 0 := by
  have h0 : coordinateEvaluation K P H ≠ 0 := by
    intro hz; apply hH; rw [← coordinateEvaluation_ker K P]; exact hz
  have h1 : coordinateEvaluation K Q (e H) ≠ 0 := by
    rw [← coordinateFieldEquiv_eval P Q e hQ H]
    exact (map_ne_zero Ψ).mpr h0
  rw [hH',map_mul]
  exact mul_ne_zero (by simpa using (map_ne_zero (algebraMap K (CoordinateField K Q))).mpr ht) h1

theorem residual_ratio (H G H' G' L : MvPolynomial (Fin 3) K) (t r : K)
    (ht : t ≠ 0) (hH : H ∉ P)
    (hH' : H'=MvPolynomial.C t*e H)
    (hG' : G'=MvPolynomial.C r*e G+L*e H) :
    movingRatio Q H' G' = algebraMap K (CoordinateField K Q) (r/t)*Ψ (movingRatio P H G)+
      MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K Q)) (coordinate K Q)
        (MvPolynomial.C t⁻¹*L) := by
  have h0 : coordinateEvaluation K P H ≠ 0 := by
    intro hz; apply hH; rw [← coordinateEvaluation_ker K P]; exact hz
  have h1 : coordinateEvaluation K Q (e H) ≠ 0 := by
    rw [← coordinateFieldEquiv_eval P Q e hQ H]
    exact (map_ne_zero Ψ).mpr h0
  have ht' : algebraMap K (CoordinateField K Q) t ≠ 0 := (map_ne_zero _).mpr ht
  have heval (A : MvPolynomial (Fin 3) K) :
      MvPolynomial.eval₂Hom (algebraMap K (CoordinateField K Q)) (coordinate K Q) A=
        coordinateEvaluation K Q A := by
    rw [coordinateEvaluation_eq_aeval]
    exact (MvPolynomial.aeval_eq_eval₂Hom _ _).symm
  rw [heval]
  unfold movingRatio
  simp only [map_div₀]
  rw [coordinateFieldEquiv_eval,coordinateFieldEquiv_eval,hH',hG']
  have hC (c : K) : coordinateEvaluation K Q (MvPolynomial.C c)=
      algebraMap K (CoordinateField K Q) c := (coordinateEvaluation K Q).commutes c
  simp only [map_add,map_mul,map_inv₀,hC]
  field_simp [h1,ht']

theorem residual_moving_weight (H G H' G' L : MvPolynomial (Fin 3) K) (t r : K)
    (ht : t ≠ 0) (hr : r ≠ 0) (hH : H ∉ P)
    (hH' : H'=MvPolynomial.C t*e H) (hG' : G'=MvPolynomial.C r*e G+L*e H)
    (hL : PolynomialInFlag unitAllFlag L) (ν : Place K (CoordinateField K Q)) :
    movingPoleTarget Q H' G' ν = movingPoleTarget P H G (placeComap Ψ ν) := by
  have hx : (fun i ↦ Ψ (coordinate K P i))=forward aY v bY aS bS cS (coordinate K Q) := by
    funext i
    exact coordinateFieldEquiv_residual_coordinate P Q aY v bY aS bS cS hv hQ i
  have hscale : PolynomialInFlag unitAllFlag (MvPolynomial.C t⁻¹*L) := by
    have hh := inFlag_mul_poly (inFlag_const (⟨0,0,0⟩ : FlagDegree) t⁻¹) hL
    have hf : (⟨0,0,0⟩ : FlagDegree)+unitAllFlag=unitAllFlag := by decide
    rw [hf] at hh
    exact hh
  have h := moving_pole_invariant ν.val (constant_value_le_one K (CoordinateField K Q) ν)
    aY v bY aS bS cS hv (coordinate K Q) (r/t) (div_ne_zero hr ht)
    (MvPolynomial.C t⁻¹*L) hscale (Ψ (movingRatio P H G)) (movingRatio Q H' G')
    (residual_ratio P Q aY v bY aS bS cS hv hQ H G H' G' L t r ht hH hH' hG')
  have hu := forward_unit_invariant ν.val (constant_value_le_one K (CoordinateField K Q) ν)
    aY v bY aS bS cS hv (coordinate K Q)
  unfold movingPole at h
  rw [hu.2.1,hu.2.2] at h
  change movingPole ν.val (coordinate K Q) (movingRatio Q H' G') =
    movingPole ν.val (fun i ↦ Ψ (coordinate K P i)) (Ψ (movingRatio P H G))
  rw [hx]
  unfold movingPole
  rw [hu.2.1,hu.2.2]
  exact h

theorem finite_sum_bound_comap {I J : Type*} (equiv : I ≃ J) (f : J → ℤ) (g : I → ℤ)
    (cost : ℕ) (hf : ∀ S : Finset J,(∑ j ∈ S,f j) ≤ (cost : ℤ))
    (heq : ∀ i,g i=f (equiv i)) : ∀ S : Finset I,(∑ i ∈ S,g i) ≤ (cost : ℤ) := by
  classical
  letI : DecidableEq I := Classical.decEq I
  letI : DecidableEq J := Classical.decEq J
  intro S
  calc
    _ = ∑ i ∈ S,f (equiv i) := Finset.sum_congr rfl (fun i _ ↦ heq i)
    _ = ∑ j ∈ S.image equiv,f j := (Finset.sum_image (fun i _ j _ h ↦ equiv.injective h)).symm
    _ ≤ _ := hf _

end
end ProximityPrize.SubmissionLower.ContactMovingBudgetTransport6719Research

namespace ProximityPrize.SubmissionLower.ContactMovingCurveBudget6719Research.MovingPoleBudget
open scoped Classical BigOperators
open ActualCurveCoordinateField CoordinateBoxZeroCount ContactSparsePoleSupportResearch
open ContactFlagBezout6543Research ContactFlagAffineResidualAutomorphismResearch
open ContactFieldPlaceTransport6719Research ContactMovingBudgetTransport6719Research
noncomputable section
set_option autoImplicit false
variable {K : Type} [Field K]
variable {P Q : Ideal (MvPolynomial (Fin 3) K)} [P.IsPrime] [Q.IsPrime]
variable {H G H' G' : MvPolynomial (Fin 3) K}

/-- .
 -/
def map_residual (budget : MovingPoleBudget P H G)
    (aY v bY aS bS cS : K) (hv : v ≠ 0)
    (hQ : Q=P.map (residualEquiv aY v bY aS bS cS hv).toRingHom)
    (L : MvPolynomial (Fin 3) K) (t r : K) (ht : t ≠ 0) (hr : r ≠ 0) (hH : H ∉ P)
    (hH' : H'=MvPolynomial.C t*(residualEquiv aY v bY aS bS cS hv H))
    (hG' : G'=MvPolynomial.C r*(residualEquiv aY v bY aS bS cS hv G)+
      L*(residualEquiv aY v bY aS bS cS hv H))
    (hL : PolynomialInFlag unitAllFlag L) : MovingPoleBudget Q H' G' where
  zCost := budget.zCost
  yzCost := budget.yzCost
  allCost := budget.allCost
  movingCost := budget.movingCost
  zPole := finite_sum_bound_comap
    (placeEquiv (coordinateFieldEquiv P Q (residualEquiv aY v bY aS bS cS hv) hQ)) _ _ _ budget.zPole
    (fun ν ↦ (residual_unit_weights P Q aY v bY aS bS cS hv hQ ν).1.symm)
  yzPole := finite_sum_bound_comap
    (placeEquiv (coordinateFieldEquiv P Q (residualEquiv aY v bY aS bS cS hv) hQ)) _ _ _ budget.yzPole
    (fun ν ↦ (residual_unit_weights P Q aY v bY aS bS cS hv hQ ν).2.1.symm)
  allPole := finite_sum_bound_comap
    (placeEquiv (coordinateFieldEquiv P Q (residualEquiv aY v bY aS bS cS hv) hQ)) _ _ _ budget.allPole
    (fun ν ↦ (residual_unit_weights P Q aY v bY aS bS cS hv hQ ν).2.2.symm)
  movingPole := finite_sum_bound_comap
    (placeEquiv (coordinateFieldEquiv P Q (residualEquiv aY v bY aS bS cS hv) hQ)) _ _ _ budget.movingPole
    (fun ν ↦ residual_moving_weight P Q aY v bY aS bS cS hv hQ
      H G H' G' L t r ht hr hH hH' hG' hL ν)

section Costs
variable (budget : MovingPoleBudget P H G)
    (aY v bY aS bS cS : K) (hv : v ≠ 0)
    (hQ : Q=P.map (residualEquiv aY v bY aS bS cS hv).toRingHom)
    (L : MvPolynomial (Fin 3) K) (t r : K) (ht : t ≠ 0) (hr : r ≠ 0) (hH : H ∉ P)
    (hH' : H'=MvPolynomial.C t*(residualEquiv aY v bY aS bS cS hv H))
    (hG' : G'=MvPolynomial.C r*(residualEquiv aY v bY aS bS cS hv G)+
      L*(residualEquiv aY v bY aS bS cS hv H)) (hL : PolynomialInFlag unitAllFlag L)
local notation "nextBudget" => budget.map_residual aY v bY aS bS cS hv hQ L t r ht hr hH hH' hG' hL

@[simp] theorem map_residual_zCost : (nextBudget).zCost=budget.zCost := rfl
@[simp] theorem map_residual_yzCost : (nextBudget).yzCost=budget.yzCost := rfl
@[simp] theorem map_residual_allCost : (nextBudget).allCost=budget.allCost := rfl
@[simp] theorem map_residual_movingCost : (nextBudget).movingCost=budget.movingCost := rfl
@[simp] theorem map_residual_weightedCost (p : FlagDegree) :
    (nextBudget).weightedCost p=budget.weightedCost p := rfl

theorem map_residual_costs :
    let next := budget.map_residual aY v bY aS bS cS hv hQ L t r ht hr hH hH' hG' hL
    next.zCost=budget.zCost ∧ next.yzCost=budget.yzCost ∧ next.allCost=budget.allCost ∧
      next.movingCost=budget.movingCost ∧ ∀ p,next.weightedCost p=budget.weightedCost p := by
  exact ⟨rfl,rfl,rfl,rfl,fun _ ↦ rfl⟩
end Costs

end
end ProximityPrize.SubmissionLower.ContactMovingCurveBudget6719Research.MovingPoleBudget
