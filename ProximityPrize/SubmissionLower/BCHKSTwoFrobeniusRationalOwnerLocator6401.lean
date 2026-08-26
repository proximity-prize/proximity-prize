import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusExtremeKernelCounter6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRationalOwnerLocator6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
noncomputable def ownerLocator
    {F ι : Type*} [Field F] (alpha : ι → F) (A : Finset ι) :
    Polynomial F :=
  ∏ i ∈ A, (Polynomial.X - Polynomial.C (alpha i))
theorem ownerLocator_natDegree
    {F ι : Type*} [Field F] (alpha : ι → F) (A : Finset ι) :
    (ownerLocator alpha A).natDegree = A.card := by
  classical
  simpa [ownerLocator] using
    (Polynomial.natDegree_finsetProd_X_sub_C_eq_card A alpha)
theorem ownerLocator_monic
    {F ι : Type*} [Field F] (alpha : ι → F) (A : Finset ι) :
    (ownerLocator alpha A).Monic := by
  classical
  simpa [ownerLocator] using Polynomial.monic_prod_X_sub_C alpha A
theorem ownerLocator_eval_eq_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    (alpha : ι → F) (A : Finset ι) (i : ι) (hi : i ∈ A) :
    (ownerLocator alpha A).eval (alpha i) = 0 := by
  classical
  simp only [ownerLocator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := i)
  · exact hi
  · simp
def ClearedRationalOwnerAgreement
    {F ι : Type*} [Field F]
    (alpha : ι → F) (A : Finset ι)
    (lambda G Q R P : Polynomial F) (z : F) : Prop :=
  ∀ i ∈ A,
    lambda.eval (alpha i) *
        (P.eval (alpha i) - z * Q.eval (alpha i)) =
      G.eval (alpha i) + z * R.eval (alpha i)
private theorem natDegree_sub_lt_of_monic_same
    {F : Type*} [Field F] (P Q : Polynomial F) (n : ℕ)
    (hn : 0 < n) (hPm : P.Monic) (hQm : Q.Monic)
    (hPd : P.natDegree = n) (hQd : Q.natDegree = n) :
    (P - Q).natDegree < n := by
  by_cases hsub : P - Q = 0
  · rw [hsub, Polynomial.natDegree_zero]
    exact hn
  · rw [Polynomial.natDegree_lt_iff_degree_lt hsub]
    have hd := Polynomial.degree_sub_lt
      (p := P) (q := Q)
      (by rw [Polynomial.degree_eq_natDegree hPm.ne_zero,
          Polynomial.degree_eq_natDegree hQm.ne_zero, hPd, hQd])
      hPm.ne_zero (by rw [hPm.leadingCoeff, hQm.leadingCoeff])
    rw [Polynomial.degree_eq_natDegree hPm.ne_zero, hPd] at hd
    exact hd
theorem ownerLocator_eq_affine_mod_denominator6401
    {F ι : Type*} [Field F] [DecidableEq ι]
    (alpha : ι ↪ F) (A : Finset ι)
    (lambda G Q R P : Polynomial F) (z : F)
    (hAcard : A.card = a6401)
    (hlambda : lambda.natDegree ≤ counterDenominatorDegree6401)
    (hGmonic : G.Monic) (hGdegree : G.natDegree = a6401)
    (hQ : Q.natDegree ≤ ownerDegreeCap6401)
    (hR : R.natDegree ≤ counterLowTermDegree6401)
    (hP : P.natDegree ≤ ownerDegreeCap6401)
    (hagree : ClearedRationalOwnerAgreement
      alpha A lambda G Q R P z) :
    ownerLocator alpha A =
      G + Polynomial.C z * R -
        lambda * (P - Polynomial.C z * Q) := by
  let L : Polynomial F := ownerLocator alpha A
  let E : Polynomial F :=
    (L - G) - Polynomial.C z * R +
      lambda * (P - Polynomial.C z * Q)
  have hLmonic : L.Monic := ownerLocator_monic alpha A
  have hLdegree : L.natDegree = a6401 := by
    simpa [L, hAcard] using ownerLocator_natDegree alpha A
  have hLG : (L - G).natDegree < a6401 :=
    natDegree_sub_lt_of_monic_same L G a6401
      (by norm_num [a6401]) hLmonic hGmonic hLdegree hGdegree
  have hzQ : (Polynomial.C z * Q).natDegree ≤ ownerDegreeCap6401 := by
    exact Polynomial.natDegree_mul_le.trans <| by
      simpa using hQ
  have hPzQ : (P - Polynomial.C z * Q).natDegree ≤
      ownerDegreeCap6401 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hP hzQ)
  have hlambdaTerm :
      (lambda * (P - Polynomial.C z * Q)).natDegree ≤
        counterLowTermDegree6401 :=
    Polynomial.natDegree_mul_le.trans <| by
      norm_num [counterDenominatorDegree6401,
        ownerDegreeCap6401] at hlambda hPzQ
      norm_num [counterLowTermDegree6401]
      omega
  have hzR : (Polynomial.C z * R).natDegree ≤
      counterLowTermDegree6401 :=
    Polynomial.natDegree_mul_le.trans <| by simpa using hR
  have hlowPred : counterLowTermDegree6401 ≤ a6401 - 1 := by
    norm_num [counterLowTermDegree6401, a6401]
  have hEdegree : E.natDegree < A.card := by
    rw [hAcard]
    apply ((Polynomial.natDegree_add_le _ _).trans <|
      max_le
        ((Polynomial.natDegree_sub_le _ _).trans <| max_le
          (Nat.le_pred_of_lt hLG) (hzR.trans hlowPred))
        (hlambdaTerm.trans hlowPred)).trans_lt
    norm_num [counterLowTermDegree6401, a6401]
  have hEeval : ∀ i ∈ A, E.eval (alpha i) = 0 := by
    intro i hi
    have howner := hagree i hi
    simp only [E, L, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C]
    rw [ownerLocator_eval_eq_zero alpha A i hi]
    linear_combination howner
  have hEzero : E = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      E (A.map alpha)
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact hEeval i hi
    · simpa using hEdegree
  dsimp [E, L] at hEzero
  linear_combination hEzero
theorem ownerLocator_top_coeff_eq6401
    {F ι : Type*} [Field F] [DecidableEq ι]
    (alpha : ι ↪ F) (A : Finset ι)
    (lambda G Q R P : Polynomial F) (z : F)
    (hidentity : ownerLocator alpha A =
      G + Polynomial.C z * R -
        lambda * (P - Polynomial.C z * Q))
    (hlambda : lambda.natDegree ≤ counterDenominatorDegree6401)
    (hQ : Q.natDegree ≤ ownerDegreeCap6401)
    (hR : R.natDegree ≤ counterLowTermDegree6401)
    (hP : P.natDegree ≤ ownerDegreeCap6401)
    (j : ℕ) (hj : counterLowTermDegree6401 < j) :
    (ownerLocator alpha A).coeff j = G.coeff j := by
  have hzQ : (Polynomial.C z * Q).natDegree ≤ ownerDegreeCap6401 :=
    Polynomial.natDegree_mul_le.trans (by simpa using hQ)
  have hPzQ : (P - Polynomial.C z * Q).natDegree ≤
      ownerDegreeCap6401 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hP hzQ)
  have hlambdaTerm :
      (lambda * (P - Polynomial.C z * Q)).natDegree ≤
        counterLowTermDegree6401 :=
    Polynomial.natDegree_mul_le.trans <| by
      norm_num [counterDenominatorDegree6401,
        ownerDegreeCap6401] at hlambda hPzQ
      norm_num [counterLowTermDegree6401]
      omega
  have hzR : (Polynomial.C z * R).natDegree ≤
      counterLowTermDegree6401 :=
    Polynomial.natDegree_mul_le.trans (by simpa using hR)
  have hczR := Polynomial.coeff_eq_zero_of_natDegree_lt (hzR.trans_lt hj)
  have hlambdaZero :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hlambdaTerm.trans_lt hj)
  have hcoeff := congrArg (fun T : Polynomial F => T.coeff j) hidentity
  simpa [Polynomial.coeff_add, Polynomial.coeff_sub, hczR,
    hlambdaZero] using hcoeff
theorem ownerLocator_inter_dvd
    {F ι : Type*} [Field F] [DecidableEq ι]
    (alpha : ι → F) (A B : Finset ι) :
    ownerLocator alpha (A ∩ B) ∣ ownerLocator alpha A := by
  classical
  exact Finset.prod_dvd_prod_of_subset (A ∩ B) A
    (fun i => Polynomial.X - Polynomial.C (alpha i))
    (Finset.inter_subset_left)
theorem rationalPencil_pair_intersection_le_153578
    {F ι : Type*} [Field F] [DecidableEq ι]
    (alpha : ι → F) (A B : Finset ι)
    (lambda G Q R Pz Pw : Polynomial F) (z w : F)
    (hAz : ownerLocator alpha A =
      G + Polynomial.C z * R -
        lambda * (Pz - Polynomial.C z * Q))
    (hBw : ownerLocator alpha B =
      G + Polynomial.C w * R -
        lambda * (Pw - Polynomial.C w * Q))
    (hlambda : lambda.natDegree ≤ counterDenominatorDegree6401)
    (hR : R.natDegree ≤ counterLowTermDegree6401)
    (hPz : Pz.natDegree ≤ ownerDegreeCap6401)
    (hPw : Pw.natDegree ≤ ownerDegreeCap6401)
    (hQ : Q.natDegree ≤ ownerDegreeCap6401)
    (hne : ownerLocator alpha A ≠ ownerLocator alpha B) :
    (A ∩ B).card ≤ counterLowTermDegree6401 := by
  let D : Polynomial F := ownerLocator alpha A - ownerLocator alpha B
  have hDne : D ≠ 0 := sub_ne_zero.mpr hne
  have hPdiff :
      ((Pz - Polynomial.C z * Q) -
        (Pw - Polynomial.C w * Q)).natDegree ≤ ownerDegreeCap6401 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_sub_le _ _).trans <|
        max_le hPz (Polynomial.natDegree_mul_le.trans <| by simpa using hQ)
    · exact (Polynomial.natDegree_sub_le _ _).trans <|
        max_le hPw (Polynomial.natDegree_mul_le.trans <| by simpa using hQ)
  have hlambdaTerm :
      (lambda * ((Pz - Polynomial.C z * Q) -
        (Pw - Polynomial.C w * Q))).natDegree ≤
          counterLowTermDegree6401 :=
    Polynomial.natDegree_mul_le.trans <| by
      norm_num [counterDenominatorDegree6401,
        ownerDegreeCap6401] at hlambda hPdiff
      norm_num [counterLowTermDegree6401]
      omega
  have hscalarR :
      (Polynomial.C (z - w) * R).natDegree ≤
        counterLowTermDegree6401 :=
    Polynomial.natDegree_mul_le.trans (by simpa using hR)
  have hDform : D = Polynomial.C (z - w) * R -
      lambda * ((Pz - Polynomial.C z * Q) -
        (Pw - Polynomial.C w * Q)) := by
    dsimp [D]
    rw [hAz, hBw]
    rw [show Polynomial.C (z - w) =
      Polynomial.C z - Polynomial.C w by simp]
    ring
  have hDdegree : D.natDegree ≤ counterLowTermDegree6401 := by
    rw [hDform]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hscalarR hlambdaTerm)
  have hinterDvd : ownerLocator alpha (A ∩ B) ∣ D :=
    dvd_sub (ownerLocator_inter_dvd alpha A B)
      (by
        rw [Finset.inter_comm]
        exact ownerLocator_inter_dvd alpha B A)
  have hinterDegree := Polynomial.natDegree_le_of_dvd hinterDvd hDne
  rw [ownerLocator_natDegree] at hinterDegree
  exact hinterDegree.trans hDdegree
theorem rationalPencil_pair_cap_still_above_message6401 :
    ownerDegreeCap6401 < counterLowTermDegree6401 ∧
      counterLowTermDegree6401 - ownerDegreeCap6401 = 22507 := by
  norm_num [ownerDegreeCap6401, counterLowTermDegree6401]
end BCHKSTwoFrobeniusRationalOwnerLocator6401
end ProximityPrize.SubmissionLower
