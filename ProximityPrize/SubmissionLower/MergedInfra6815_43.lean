import ProximityPrize.SubmissionLower.MergedInfra6815_41
import ProximityPrize.SubmissionLower.MergedInfra6815_32
set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.RamifiedOwnerDerivative6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial WholeSpaceCube6814 WholeSpaceCubeUniform6814
open SecondJetCoefficients SecondJetCoefficientSpecialization
open MovingSourceOwnerSplit6814 MovingSourceCoupledClearing6814
open MovingSourceCarrierField6814 MovingFiberThreeSources6811
open SecondJetCarrierDichotomy RCN234 RCN156

variable {K : Type} [Field K] [CharP K 2130706433]

theorem derivative_ne_zero (J : Poly (K:=K)) (hJ : J≠0)
    (hn : 0<(asS J).natDegree) (hsmall : (asS J).natDegree<2130706433) :
    (asS J).derivative≠0 := by
  have hA : asS J≠0 := by simpa using hJ
  have hcast : (((asS J).natDegree : ℕ) : MvPolynomial (Fin 4) K)≠0 := by
    intro hz
    have hd := (CharP.cast_eq_zero_iff (MvPolynomial (Fin 4) K) 2130706433 _).mp hz
    exact (not_le_of_gt hsmall) (Nat.le_of_dvd hn hd)
  have hcoeff : (asS J).coeff (asS J).natDegree≠0 := by
    simpa only [Polynomial.coeff_natDegree] using (Polynomial.leadingCoeff_ne_zero.mpr hA)
  have hc := mul_ne_zero hcoeff hcast
  intro hz
  have he := congrArg (fun P : Polynomial (MvPolynomial (Fin 4) K) =>
    P.coeff ((asS J).natDegree-1)) hz
  have heq : (asS J).natDegree-1+1=(asS J).natDegree := by omega
  have heqCast : (((asS J).natDegree-1 : ℕ) : MvPolynomial (Fin 4) K)+1=
      ((asS J).natDegree : MvPolynomial (Fin 4) K) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      congrArg (fun n : ℕ => (n : MvPolynomial (Fin 4) K)) heq
  rw [Polynomial.coeff_derivative,Polynomial.coeff_zero,heq,heqCast] at he
  exact hc he

theorem pderiv_nonzero_coprime (J : Poly (K:=K)) (hJ : Irreducible J)
    (hn : 0<(asS J).natDegree) (hsmall : (asS J).natDegree<2130706433) :
    pderiv 1 J≠0 ∧ IsRelPrime J (pderiv 1 J) := by
  have hd := derivative_ne_zero J hJ.ne_zero hn hsmall
  have hne : pderiv 1 J≠0 := by
    intro hz
    apply hd
    rw [← asS_pderiv,hz,map_zero]
  refine ⟨hne,hJ.isRelPrime_iff_not_dvd.mpr ?_⟩
  intro hdiv
  have hm : asS J∣asS (pderiv 1 J) := map_dvd (asS (K:=K)).toRingHom hdiv
  rw [asS_pderiv] at hm
  have hle := Polynomial.natDegree_le_of_dvd hm hd
  have hlt := Polynomial.natDegree_derivative_lt (by omega : (asS J).natDegree≠0)
  omega

omit [CharP K 2130706433] in
theorem pderiv_weight (J : Poly (K:=K)) (weights : Fin 5 → ℕ) :
    weightedTotalDegree weights (pderiv 1 J)≤weightedTotalDegree weights J-weights 1 := by
  apply Finset.sup_le
  intro d hd
  have hs : d+Finsupp.single 1 1∈J.support := by
    simpa using SecondJetGlobalDifferentiation.support_iterate J 1 d (by simpa using hd)
  have hh := MvPolynomial.le_weightedTotalDegree weights hs
  simp only [map_add,Finsupp.weight_single,one_nsmul] at hh
  omega

omit [CharP K 2130706433] in
theorem pderiv_order (J : Poly (K:=K)) : (pderiv 1 J).degreeOf 1≤J.degreeOf 1-1 := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hs : d+Finsupp.single 1 1∈J.support := by
    simpa using SecondJetGlobalDifferentiation.support_iterate J 1 d (by simpa using hd)
  have hh := MvPolynomial.monomial_le_degreeOf 1 hs
  simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
  omega

omit [CharP K 2130706433] in
theorem derivative_root_power {E : Type} [Field E]
    (phi : MvPolynomial (Fin 4) K →+* E) (z : E) (J : Poly (K:=K)) (m : ℕ)
    (hm : ((asS J).map phi).rootMultiplicity z=m) :
    (Polynomial.X-Polynomial.C z)^(m-1)∣(asS (pderiv 1 J)).map phi := by
  have hp := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd
    (Polynomial.pow_rootMultiplicity_dvd ((asS J).map phi) z)
  rw [hm] at hp
  simpa only [asS_pderiv,Polynomial.derivative_map] using hp

theorem source_pair_of_ramified_owner
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (hpos : 0<F.degreeOf 2) (hFsmall : F.degreeOf 2<2130706433)
    (J : Poly (K:=K)) (hJ : Irreducible J) (hT : total J≤1700)
    (hn : 0<(asS J).natDegree) (hsmall : (asS J).natDegree<2130706433)
    (m : ℕ) (hm : 2≤m)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m) :
    ∃ A B : Source F, A.P=J ∧ B.P=pderiv 1 J ∧ IsRelPrime A.P B.P ∧
      m≤A.d ∧ m-1≤B.d ∧
      (∀ weights : Fin 5 → ℕ,
        weightedTotalDegree weights B.P≤weightedTotalDegree weights J-weights 1) := by
  obtain ⟨hne,hcop⟩ := pderiv_nonzero_coprime J hJ hn hsmall
  have hTQ : total (pderiv 1 J)≤1700 :=
    (pderiv_weight J totalWeights).trans ((Nat.sub_le _ _).trans hT)
  have hpowJ : (Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^m∣(asS J).map (carrierMap F) := by
    rw [← hroot]
    exact Polynomial.pow_rootMultiplicity_dvd _ _
  obtain ⟨A,hAJ,hAm⟩ := WholeSpacePowerSourcePair6814.source_of_small_power
    F hFT hpos hFsmall J hJ.ne_zero hT m (by omega) hpowJ
  obtain ⟨B,hBQ,hBm⟩ := WholeSpacePowerSourcePair6814.source_of_small_power
    F hFT hpos hFsmall (pderiv 1 J) hne hTQ (m-1) (by omega)
    (derivative_root_power (carrierMap F) (ratio (carrierMap F) F) J m hroot)
  refine ⟨A,B,hAJ,hBQ,?_,hAm,hBm,?_⟩
  · simpa only [hAJ,hBQ] using hcop
  · intro weights
    simpa only [hBQ] using pderiv_weight J weights

end
end ProximityPrize.SubmissionLower.RamifiedOwnerDerivative6815
end MergedPart0
section MergedPart1
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
end MergedPart1
