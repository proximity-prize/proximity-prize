import ProximityPrize.SubmissionLower.RamifiedOwnerDerivative6815
import ProximityPrize.SubmissionLower.MovingSourceTripleOwnerExclusion6814
namespace ProximityPrize.SubmissionLower.QuadraticRamifiedOwner6815
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 600000
open Polynomial MvPolynomial RCN234 RCN156
open WholeSpaceCube6814 WholeSpaceCubeUniform6814
open SecondJetCoefficients SecondJetCarrierDichotomy MovingSourceCarrierField6814
open MovingSourceCoupledClearing6814
open MovingSourceTripleOwnerExclusion6814 RamifiedOwnerDerivative6815

def disc {A : Type*} [CommRing A] (P : Polynomial A) : A :=
  P.coeff 1 ^ 2 - 4 * P.coeff 2 * P.coeff 0

theorem quadratic_form {A : Type*} [CommRing A] (P : Polynomial A)
    (h : P.natDegree ≤ 2) :
    P = Polynomial.C (P.coeff 2)*Polynomial.X^2 +
      Polynomial.C (P.coeff 1)*Polynomial.X + Polynomial.C (P.coeff 0) := by
  have hh := P.as_sum_range_C_mul_X_pow' (show P.natDegree < 3 by omega)
  conv_lhs => rw [hh]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one]
  ring

theorem derivative_square {A : Type*} [CommRing A] (P : Polynomial A)
    (h : P.natDegree ≤ 2) :
    P.derivative ^ 2 = Polynomial.C (4*P.coeff 2)*P + Polynomial.C (disc P) := by
  have hf := quadratic_form P h
  have hd : P.derivative = Polynomial.C (2*P.coeff 2)*Polynomial.X +
      Polynomial.C (P.coeff 1) := by
    conv_lhs => rw [hf]
    simp only [derivative_add,derivative_C_mul,derivative_X_pow,derivative_X,
      derivative_C,add_zero,mul_one]
    norm_num
    ring
  rw [hd]
  conv_rhs => lhs; rhs; rw [hf]
  simp only [disc,map_sub,map_mul,map_pow,map_ofNat]
  ring

theorem disc_eq_zero_of_double_root {E : Type*} [Field E]
    (P : Polynomial E) (h : P.natDegree ≤ 2) (z : E)
    (hp : 2 ≤ P.rootMultiplicity z) : disc P = 0 := by
  have h0 : P.eval z = 0 := (Polynomial.rootMultiplicity_pos'.mp (by omega)).2
  have h1 : P.derivative.eval z = 0 := by
    simpa using (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (p := P) (t := z) (n := 1) (by omega))
  have he := congrArg (Polynomial.eval z) (derivative_square P h)
  simpa only [Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,h0,h1,zero_pow (by decide : 2≠0),
    mul_zero,zero_add] using he.symm

variable {K : Type} [Field K] [CharP K 2130706433]

theorem quadratic_rootMultiplicity_lt_two
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : MvPolynomial (Fin 5) K) (hJ : Irreducible J)
    (T : ℕ) (hT : total J ≤ T) (hF : 2*T < wt residualTotalWeights F)
    (hs : (asS J).natDegree = 2) :
    ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F) < 2 := by
  by_contra hn
  let P := asS J
  have hz : disc (P.map (carrierMap F)) = 0 := disc_eq_zero_of_double_root _
    (Polynomial.natDegree_map_le.trans (show P.natDegree≤2 by dsimp [P]; omega))
    (ratio (carrierMap F) F) (by simpa only [P] using (Nat.le_of_not_gt hn))
  have hdiv : F ∣ disc P := (carrierMap_zero_iff F _).mp (by
    simpa only [disc,Polynomial.coeff_map,map_sub,map_mul,map_pow,map_ofNat] using hz)
  have hcoeff (j : ℕ) : wt residualTotalWeights (P.coeff j) ≤ T :=
    source_coefficient_total_cap J T hT j
  have hdisc : wt residualTotalWeights (disc P) ≤ 2*T := by
    have h1 := (wt_pow_le residualTotalWeights (P.coeff 1) 2).trans
      (Nat.mul_le_mul_left 2 (hcoeff 1))
    have h2 := wt_mul_le residualTotalWeights (4 : MvPolynomial (Fin 4) K) (P.coeff 2)
    have h3 := wt_mul_le residualTotalWeights ((4 : MvPolynomial (Fin 4) K)*P.coeff 2) (P.coeff 0)
    have h4 : wt residualTotalWeights ((4 : MvPolynomial (Fin 4) K)*P.coeff 2*P.coeff 0)≤2*T := by
      have hc4 : wt residualTotalWeights (4 : MvPolynomial (Fin 4) K)=0 := wt_natCast _ 4
      rw [hc4] at h2
      have hh := hcoeff 2
      have hh0 := hcoeff 0
      omega
    exact (wt_sub_le _ _ _).trans (max_le h1 h4)
  have hzero : disc P = 0 := by
    by_contra hne
    have hh := RCN081.weightedTotalDegree_le_of_dvd residualTotalWeights F (disc P) hdiv hne
    change wt residualTotalWeights F ≤ wt residualTotalWeights (disc P) at hh
    omega
  have hirr : Irreducible P := (MulEquiv.irreducible_iff
    (f := (asS (K:=K)).toMulEquiv)).mpr hJ
  have hidentity := derivative_square P (show P.natDegree≤2 by dsimp [P]; omega)
  rw [hzero,map_zero,add_zero] at hidentity
  have hpow : P ∣ P.derivative ^ 2 := by
    rw [hidentity]
    exact dvd_mul_left _ _
  have hderiv : P ∣ P.derivative := hirr.prime.dvd_of_dvd_pow hpow
  have hne : P.derivative ≠ 0 := derivative_ne_zero J hJ.ne_zero (by omega) (by omega)
  have hle := Polynomial.natDegree_le_of_dvd hderiv hne
  have hlt := Polynomial.natDegree_derivative_lt (show P.natDegree≠0 by dsimp [P]; omega)
  omega

end
end ProximityPrize.SubmissionLower.QuadraticRamifiedOwner6815
