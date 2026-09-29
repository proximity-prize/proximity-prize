import ProximityPrize.SubmissionLower.MovingSourceCoupledClearing6814

/-! Two coprime factors of the same actual small source share ALL degree
budgets. The ordinary flags retain that coupling through S clearing. -/
namespace ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 400000
open MvPolynomial RCN095 WholeSpaceCube6814 WholeSpaceCubeUniform6814
open MovingSourceCoupledClearing6814 MovingFiberThreeSources6811 MovingSourceTwoProfiles6814

variable {K : Type} [Field K]
local notation "Poly5" => MvPolynomial (Fin 5) K

theorem pair_degrees_le (P J D : Poly5) (hP : P≠0) (hJ : J≠0) (hD : D≠0)
    (hcop : IsRelPrime J D) (hJP : J∣P) (hDP : D∣P) :
    (∀ w : Fin 5 → ℕ, weightedTotalDegree w J+weightedTotalDegree w D≤weightedTotalDegree w P) ∧
      order J+order D≤order P := by
  obtain ⟨R,hR⟩ := hcop.mul_dvd hJP hDP
  have hRne : R≠0 := by intro hz; apply hP; rw [hR,hz,mul_zero]
  constructor
  · intro w
    rw [hR,weight_mul _ _ _ (mul_ne_zero hJ hD) hRne,weight_mul _ _ _ hJ hD]
    omega
  · change J.degreeOf 1+D.degreeOf 1≤P.degreeOf 1
    rw [hR,degreeOf_mul_eq (mul_ne_zero hJ hD) hRne,degreeOf_mul_eq hJ hD]
    omega

theorem same_source_flag_budgets
    (F : MvPolynomial (Fin 4) K) (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (J D : Poly5) (hJ : J≠0) (hD : D≠0) (hcop : IsRelPrime J D) (hJP : J∣S.P) (hDP : D∣S.P)
    (hsJ : 0<order J) (hsD : 0<order D) :
    2≤(ordinaryFlag J).all ∧ 2≤(ordinaryFlag D).all ∧
    (ordinaryFlag J).all+(ordinaryFlag D).all≤31 ∧
    (ordinaryFlag J).yz+(ordinaryFlag J).all+(ordinaryFlag D).yz+(ordinaryFlag D).all≤112 ∧
    (ordinaryFlag J).zOnly+(ordinaryFlag J).yz+(ordinaryFlag J).all+
      (ordinaryFlag D).zOnly+(ordinaryFlag D).yz+(ordinaryFlag D).all≤1009 := by
  have hp := pair_degrees_le S.P J D (source_nonzero F S) hJ hD hcop hJP hDP
  have hcap := MovingSourceOwnerRouting6814.source_caps F S
  rcases hS with ⟨hB,hU,hT,hdeg,hk,hn⟩
  rw [hB,hU,hT,hdeg] at hcap
  have hb : slope J+slope D≤31 := (hp.1 slopeWeights).trans hcap.1
  have hu : middle J+middle D≤98 := (hp.1 middleWeights).trans hcap.2.1
  have ht : total J+total D≤995 := (hp.1 totalWeights).trans hcap.2.2.1
  have hs : order J+order D≤14 := hp.2.trans hcap.2.2.2
  have hnj := source_nested J
  have hnd := source_nested D
  have hcj := ordinaryFlag_cumulative J
  have hcd := ordinaryFlag_cumulative D
  omega

theorem same_source_pair_prices
    (F : MvPolynomial (Fin 4) K) (S : Source F) (hS : Profile S 31 98 995 14 2 3)
    (J D : Poly5) (hJ : J≠0) (hD : D≠0) (hcop : IsRelPrime J D) (hJP : J∣S.P) (hDP : D∣S.P)
    (hsJ : 0<order J) (hsD : 0<order D) :
    flagMixed (ordinaryFlag J) (ordinaryFlag D) unitZFlag≤2407 ∧
    flagMixed (ordinaryFlag J) (ordinaryFlag D) unitYZFlag≤28420 ∧
    flagMixed (ordinaryFlag J) (ordinaryFlag D) unitAllFlag≤98890 := by
  obtain ⟨hj,hd,hb,hu,ht⟩ := same_source_flag_budgets F S hS J D hJ hD hcop hJP hDP hsJ hsD
  exact UniqueCurvatureOwner6814.small_source_pair_prices _ _ hj hd hb hu ht

/-- Root ownership of a divisor of a nonzero mapped source forces a
positive S degree. No S-dependence premise is invented for that divisor. -/
theorem factor_order_pos_of_root {E : Type} [Field E]
    (phi : MvPolynomial (Fin 4) K →+* E) (z : E) (P J : Poly5)
    (hne : MovingSourceOwnerSplit6814.rootPolynomialMap phi P≠0) (hdiv : J∣P)
    (hroot : MovingSourceOwnerSplit6814.rootEvaluation phi z J=0) : 0<order J := by
  have hJne : MovingSourceOwnerSplit6814.rootPolynomialMap phi J≠0 := by
    intro hz
    have hd := map_dvd (MovingSourceOwnerSplit6814.rootPolynomialMap phi) hdiv
    rw [hz,zero_dvd_iff] at hd
    exact hne hd
  have hm := (Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hd := Polynomial.natDegree_le_of_dvd
    ((MovingSourceOwnerSplit6814.rootPolynomialMap phi J).pow_rootMultiplicity_dvd z) hJne
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hd
  have hn : (MovingSourceOwnerSplit6814.rootPolynomialMap phi J).natDegree≤order J :=
    Polynomial.natDegree_map_le.trans_eq (MovingSourceNativeFactor6814.asS_natDegree J)
  omega

#print axioms same_source_pair_prices
#print axioms factor_order_pos_of_root
end
end ProximityPrize.SubmissionLower.MovingSourceSameSourceBudget6814
