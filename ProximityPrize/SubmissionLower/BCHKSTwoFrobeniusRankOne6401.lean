import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRank6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRankOne6401
open Polynomial
open BCHKSTwoFrobeniusRank6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
noncomputable def HomogeneousRelation {K : Type*} [Field K]
    (sigma : K →+* K) (A₁ A₂ P : Polynomial K) : Prop :=
  A₁ * P + A₂ * twist sigma P = 0
noncomputable def FrobeniusFixedPolynomial {K : Type*} [Field K]
    (sigma : K →+* K) (P : Polynomial K) : Prop :=
  twist sigma P = P
noncomputable def FrobeniusFixedRatio {K : Type*} [Field K]
    (sigma : K →+* K) (P Q : Polynomial K) : Prop :=
  twist sigma P * Q = P * twist sigma Q
theorem difference_homogeneous_of_affine_solutions
    {K : Type*} [Field K] (sigma : K →+* K)
    (q : BoundedTriple K) (P Q : Polynomial K)
    (hP : relationPolynomial sigma q P = 0)
    (hQ : relationPolynomial sigma q Q = 0) :
    HomogeneousRelation sigma (q.2.1 : Polynomial K)
      (q.2.2 : Polynomial K) (P - Q) := by
  unfold relationPolynomial HomogeneousRelation twist at *
  rw [Polynomial.map_sub]
  linear_combination hP - hQ
theorem frobeniusFixedRatio_of_homogeneous_solutions
    {K : Type*} [Field K] (sigma : K →+* K)
    (A₁ A₂ P Q : Polynomial K)
    (hnontrivial : A₁ ≠ 0 ∨ A₂ ≠ 0)
    (hP : HomogeneousRelation sigma A₁ A₂ P)
    (hQ : HomogeneousRelation sigma A₁ A₂ Q) :
    FrobeniusFixedRatio sigma P Q := by
  rcases hnontrivial with hA₁ | hA₂
  · have hmul : A₁ *
        (twist sigma P * Q - P * twist sigma Q) = 0 := by
      unfold HomogeneousRelation at hP hQ
      linear_combination
        -(twist sigma Q) * hP + (twist sigma P) * hQ
    have hzero := (mul_eq_zero.mp hmul).resolve_left hA₁
    exact sub_eq_zero.mp hzero
  · have hmul : A₂ *
        (twist sigma P * Q - P * twist sigma Q) = 0 := by
      unfold HomogeneousRelation at hP hQ
      linear_combination Q * hP - P * hQ
    have hzero := (mul_eq_zero.mp hmul).resolve_left hA₂
    exact sub_eq_zero.mp hzero
theorem affine_solution_displacement_ratio_fixed
    {K : Type*} [Field K] (sigma : K →+* K)
    (q : BoundedTriple K) (P₀ P₁ P : Polynomial K)
    (hnontrivial : (q.2.1 : Polynomial K) ≠ 0 ∨
      (q.2.2 : Polynomial K) ≠ 0)
    (hP₀ : relationPolynomial sigma q P₀ = 0)
    (hP₁ : relationPolynomial sigma q P₁ = 0)
    (hP : relationPolynomial sigma q P = 0) :
    FrobeniusFixedRatio sigma (P - P₀) (P₁ - P₀) := by
  apply frobeniusFixedRatio_of_homogeneous_solutions sigma
    (q.2.1 : Polynomial K) (q.2.2 : Polynomial K)
  · exact hnontrivial
  · exact difference_homogeneous_of_affine_solutions sigma q P P₀ hP hP₀
  · exact difference_homogeneous_of_affine_solutions sigma q P₁ P₀ hP₁ hP₀
noncomputable def BoundedFixedGenerator {K : Type*} [Field K]
    (sigma : K →+* K) (A₁ A₂ : Polynomial K) (degreeCap : ℕ) : Prop :=
  ∃ h : Polynomial K,
    h ≠ 0 ∧
    h.natDegree ≤ degreeCap ∧
    HomogeneousRelation sigma A₁ A₂ h ∧
    ∀ D : Polynomial K,
      D.natDegree ≤ degreeCap →
      HomogeneousRelation sigma A₁ A₂ D →
      ∃ R : Polynomial K,
        FrobeniusFixedPolynomial sigma R ∧ D = h * R
theorem exists_fixed_quotient_of_minimal_homogeneous_solution
    {K : Type*} [Field K] (sigma : K →+* K)
    (A₁ A₂ h D : Polynomial K)
    (hnontrivial : A₁ ≠ 0 ∨ A₂ ≠ 0)
    (hh : h ≠ 0)
    (hhrel : HomogeneousRelation sigma A₁ A₂ h)
    (hDrel : HomogeneousRelation sigma A₁ A₂ D)
    (hminimal : ∀ R : Polynomial K, R ≠ 0 →
      HomogeneousRelation sigma A₁ A₂ R → h.natDegree ≤ R.natDegree) :
    ∃ Q : Polynomial K,
      FrobeniusFixedPolynomial sigma Q ∧ D = h * Q := by
  let Q : Polynomial K := D / h
  let R : Polynomial K := D % h
  have hdecomp : h * Q + R = D := by
    exact EuclideanDomain.div_add_mod D h
  have hratio : FrobeniusFixedRatio sigma D h :=
    frobeniusFixedRatio_of_homogeneous_solutions sigma A₁ A₂ D h
      hnontrivial hDrel hhrel
  have htwisth : twist sigma h ≠ 0 := by
    unfold twist
    exact (Polynomial.map_ne_zero_iff sigma.injective).2 hh
  have hQfixed : FrobeniusFixedPolynomial sigma Q := by
    by_contra hnot
    have hdiff : twist sigma Q - Q ≠ 0 := sub_ne_zero.mpr hnot
    have hcross :
        (h * twist sigma h) * (twist sigma Q - Q) =
          R * twist sigma h - twist sigma R * h := by
      unfold FrobeniusFixedRatio at hratio
      rw [← hdecomp] at hratio
      unfold twist at hratio ⊢
      simp only [Polynomial.map_add, Polynomial.map_mul] at hratio ⊢
      linear_combination hratio
    by_cases hR : R = 0
    · have hcross' := hcross
      rw [hR] at hcross'
      unfold twist at hcross'
      simp only [Polynomial.map_zero, zero_mul, sub_zero] at hcross'
      exact hdiff ((mul_eq_zero.mp hcross').resolve_left
        (mul_ne_zero hh htwisth))
    · have hRdeg : R.natDegree < h.natDegree := by
        rw [Polynomial.natDegree_lt_iff_degree_lt hR]
        simpa [Polynomial.degree_eq_natDegree hh] using
          (Polynomial.degree_mod_lt D hh)
      have htwistR : twist sigma R ≠ 0 := by
        unfold twist
        exact (Polynomial.map_ne_zero_iff sigma.injective).2 hR
      have hleft :
          ((h * twist sigma h) * (twist sigma Q - Q)).natDegree =
            h.natDegree + h.natDegree +
              (twist sigma Q - Q).natDegree := by
        rw [Polynomial.natDegree_mul (mul_ne_zero hh htwisth) hdiff,
          Polynomial.natDegree_mul hh htwisth]
        simp [twist, Polynomial.natDegree_map sigma]
      have hright :
          (R * twist sigma h - twist sigma R * h).natDegree <
            h.natDegree + h.natDegree := by
        apply lt_of_le_of_lt
          (Polynomial.natDegree_sub_le (R * twist sigma h)
            (twist sigma R * h))
        rw [Polynomial.natDegree_mul hR htwisth,
          Polynomial.natDegree_mul htwistR hh]
        simp only [twist, Polynomial.natDegree_map sigma]
        omega
      rw [hcross] at hleft
      omega
  have hRrel : HomogeneousRelation sigma A₁ A₂ R := by
    unfold HomogeneousRelation at hDrel hhrel ⊢
    rw [← hdecomp] at hDrel
    unfold twist at hDrel hhrel ⊢
    simp only [Polynomial.map_add, Polynomial.map_mul] at hDrel ⊢
    unfold FrobeniusFixedPolynomial twist at hQfixed
    rw [hQfixed] at hDrel
    linear_combination hDrel - Q * hhrel
  have hRzero : R = 0 := by
    by_contra hR
    have hRdeg : R.natDegree < h.natDegree := by
      rw [Polynomial.natDegree_lt_iff_degree_lt hR]
      simpa [Polynomial.degree_eq_natDegree hh] using
        (Polynomial.degree_mod_lt D hh)
    exact (not_le_of_gt hRdeg) (hminimal R hR hRrel)
  refine ⟨Q, hQfixed, ?_⟩
  rw [← hdecomp, hRzero, add_zero]
theorem boundedFixedGenerator_of_exists_nonzero_solution
    {K : Type*} [Field K] (sigma : K →+* K)
    (A₁ A₂ : Polynomial K) (degreeCap : ℕ)
    (hnontrivial : A₁ ≠ 0 ∨ A₂ ≠ 0)
    (hexists : ∃ D : Polynomial K,
      D ≠ 0 ∧ D.natDegree ≤ degreeCap ∧
        HomogeneousRelation sigma A₁ A₂ D) :
    BoundedFixedGenerator sigma A₁ A₂ degreeCap := by
  let degrees : Set ℕ := {d | ∃ D : Polynomial K,
    D ≠ 0 ∧ HomogeneousRelation sigma A₁ A₂ D ∧ D.natDegree = d}
  have hdegrees : degrees.Nonempty := by
    obtain ⟨D, hD, _hDdeg, hDrel⟩ := hexists
    exact ⟨D.natDegree, D, hD, hDrel, rfl⟩
  have hminmem := Nat.sInf_mem hdegrees
  obtain ⟨h, hh, hhrel, hhdegree⟩ := hminmem
  have hminimal : ∀ R : Polynomial K, R ≠ 0 →
      HomogeneousRelation sigma A₁ A₂ R → h.natDegree ≤ R.natDegree := by
    intro R hR hRrel
    rw [hhdegree]
    exact Nat.sInf_le ⟨R, hR, hRrel, rfl⟩
  obtain ⟨D, hD, hDdeg, hDrel⟩ := hexists
  have hhdeg : h.natDegree ≤ degreeCap :=
    (hminimal D hD hDrel).trans hDdeg
  refine ⟨h, hh, hhdeg, hhrel, ?_⟩
  intro E _hEdeg hErel
  exact exists_fixed_quotient_of_minimal_homogeneous_solution
    sigma A₁ A₂ h E hnontrivial hh hhrel hErel hminimal
theorem boundedFixedGenerator_of_distinct_affine_solutions
    {K : Type*} [Field K] (sigma : K →+* K)
    (q : BoundedTriple K) (degreeCap : ℕ)
    (hnontrivial : (q.2.1 : Polynomial K) ≠ 0 ∨
      (q.2.2 : Polynomial K) ≠ 0)
    (P₀ P₁ : Polynomial K)
    (hP₀deg : P₀.natDegree ≤ degreeCap)
    (hP₁deg : P₁.natDegree ≤ degreeCap)
    (hP₀ : relationPolynomial sigma q P₀ = 0)
    (hP₁ : relationPolynomial sigma q P₁ = 0)
    (hne : P₁ ≠ P₀) :
    BoundedFixedGenerator sigma (q.2.1 : Polynomial K)
      (q.2.2 : Polynomial K) degreeCap := by
  apply boundedFixedGenerator_of_exists_nonzero_solution
    sigma (q.2.1 : Polynomial K) (q.2.2 : Polynomial K)
      degreeCap hnontrivial
  refine ⟨P₁ - P₀, sub_ne_zero.mpr hne, ?_, ?_⟩
  · exact (Polynomial.natDegree_sub_le P₁ P₀).trans
      (max_le hP₁deg hP₀deg)
  · exact difference_homogeneous_of_affine_solutions
      sigma q P₁ P₀ hP₁ hP₀
noncomputable def FixedPolynomialDescent
    {F K : Type*} [Field F] [Field K]
    (embed : F →+* K) (sigma : K →+* K) : Prop :=
  ∀ R : Polynomial K,
    FrobeniusFixedPolynomial sigma R →
    ∃ Rbase : Polynomial F, R = Rbase.map embed
def fixedCoefficientField {K : Type*} [Field K]
    (sigma : K →+* K) : Subfield K where
  carrier := {x | sigma x = x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]
private noncomputable def toFixedCoefficient
    {K : Type*} [Field K] (sigma : K →+* K) (a : K) :
    fixedCoefficientField sigma := by
  letI : DecidableEq K := Classical.decEq K
  exact if ha : sigma a = a then ⟨a, ha⟩ else 0
private theorem toFixedCoefficient_zero
    {K : Type*} [Field K] (sigma : K →+* K) :
    toFixedCoefficient sigma 0 = 0 := by
  apply Subtype.ext
  simp [toFixedCoefficient]
private noncomputable def descendFixedPolynomial
    {K : Type*} [Field K] (sigma : K →+* K) (P : Polynomial K) :
    Polynomial (fixedCoefficientField sigma) :=
  Polynomial.ofFinsupp <|
    AddMonoidAlgebra.ofCoeff <|
      Finsupp.mapRange (toFixedCoefficient sigma)
        (toFixedCoefficient_zero sigma) P.toFinsupp.coeff
theorem map_descendFixedPolynomial_of_fixed
    {K : Type*} [Field K] (sigma : K →+* K) (P : Polynomial K)
    (hP : FrobeniusFixedPolynomial sigma P) :
    (descendFixedPolynomial sigma P).map
        (fixedCoefficientField sigma).subtype = P := by
  ext n
  have hn : sigma (P.coeff n) = P.coeff n := by
    have hcoeff := congrArg (fun Q : Polynomial K => Q.coeff n) hP
    simpa [FrobeniusFixedPolynomial, twist] using hcoeff
  have hn' : sigma (P.toFinsupp.coeff n) = P.toFinsupp.coeff n := by
    simpa only [Polynomial.toFinsupp_apply] using hn
  simp [descendFixedPolynomial, toFixedCoefficient,
    Polynomial.toFinsupp_apply]
  rw [dif_pos hn']
theorem fixedPolynomialDescent_to_fixedCoefficientField
    {K : Type*} [Field K] (sigma : K →+* K) :
    FixedPolynomialDescent (fixedCoefficientField sigma).subtype sigma := by
  intro R hR
  exact ⟨descendFixedPolynomial sigma R,
    (map_descendFixedPolynomial_of_fixed sigma R hR).symm⟩
theorem quotient_natDegree_le_sub
    {K : Type*} [Field K] (h R D : Polynomial K) (degreeCap : ℕ)
    (hh : h ≠ 0) (hhdeg : h.natDegree ≤ degreeCap)
    (hDdeg : D.natDegree ≤ degreeCap) (hfactor : D = h * R) :
    R.natDegree ≤ degreeCap - h.natDegree := by
  by_cases hR : R = 0
  · subst hR
    simp
  · have hmul := Polynomial.natDegree_mul hh hR
    rw [hfactor, hmul] at hDdeg
    omega
theorem exists_fixed_multiplier_of_boundedGenerator
    {K : Type*} [Field K] (sigma : K →+* K)
    (q : BoundedTriple K) (degreeCap : ℕ)
    (hgen : BoundedFixedGenerator sigma (q.2.1 : Polynomial K)
      (q.2.2 : Polynomial K) degreeCap)
    (P₀ P : Polynomial K)
    (hP₀deg : P₀.natDegree ≤ degreeCap)
    (hPdeg : P.natDegree ≤ degreeCap)
    (hP₀ : relationPolynomial sigma q P₀ = 0)
    (hP : relationPolynomial sigma q P = 0) :
    ∃ h R : Polynomial K,
      h ≠ 0 ∧
      h.natDegree ≤ degreeCap ∧
      FrobeniusFixedPolynomial sigma R ∧
      R.natDegree ≤ degreeCap - h.natDegree ∧
      P = P₀ + h * R := by
  obtain ⟨h, hh, hhdeg, _hhrel, hgenerate⟩ := hgen
  have hDdeg : (P - P₀).natDegree ≤ degreeCap := by
    exact (Polynomial.natDegree_sub_le P P₀).trans (max_le hPdeg hP₀deg)
  have hDrel := difference_homogeneous_of_affine_solutions
    sigma q P P₀ hP hP₀
  obtain ⟨R, hRfixed, hfactor⟩ := hgenerate (P - P₀) hDdeg hDrel
  refine ⟨h, R, hh, hhdeg, hRfixed,
    quotient_natDegree_le_sub h R (P - P₀) degreeCap hh hhdeg hDdeg hfactor, ?_⟩
  linear_combination hfactor
theorem exists_base_multiplier_of_generator_and_descent
    {F K : Type*} [Field F] [Field K]
    (embed : F →+* K) (sigma : K →+* K)
    (q : BoundedTriple K) (degreeCap : ℕ)
    (hgen : BoundedFixedGenerator sigma (q.2.1 : Polynomial K)
      (q.2.2 : Polynomial K) degreeCap)
    (hdescent : FixedPolynomialDescent embed sigma)
    (P₀ P : Polynomial K)
    (hP₀deg : P₀.natDegree ≤ degreeCap)
    (hPdeg : P.natDegree ≤ degreeCap)
    (hP₀ : relationPolynomial sigma q P₀ = 0)
    (hP : relationPolynomial sigma q P = 0) :
    ∃ h : Polynomial K, ∃ Rbase : Polynomial F,
      h ≠ 0 ∧
      h.natDegree ≤ degreeCap ∧
      Rbase.natDegree ≤ degreeCap - h.natDegree ∧
      P = P₀ + h * Rbase.map embed := by
  obtain ⟨h, R, hh, hhdeg, hRfixed, hRdeg, hfactor⟩ :=
    exists_fixed_multiplier_of_boundedGenerator sigma q degreeCap hgen
      P₀ P hP₀deg hPdeg hP₀ hP
  obtain ⟨Rbase, hRbase⟩ := hdescent R hRfixed
  subst R
  refine ⟨h, Rbase, hh, hhdeg, ?_, hfactor⟩
  simpa [Polynomial.natDegree_map embed] using hRdeg
theorem shortened_johnson_defect_formula6401 (t : ℤ) :
    (185354 - t) ^ 2 - (262144 - t) * (131071 - t) =
      -3370908 + 22507 * t := by
  ring
theorem shortened_johnson_threshold6401 :
    ((185354 - 149 : ℤ) ^ 2 -
        (262144 - 149) * (131071 - 149) = -17365) ∧
      ((185354 - 150 : ℤ) ^ 2 -
        (262144 - 150) * (131071 - 150) = 5142) := by
  norm_num
theorem shortened_johnson_positive_of_generator_degree_ge150
    (t : ℕ) (ht : 150 ≤ t) (_htop : t ≤ 131071) :
    0 < ((185354 : ℤ) - t) ^ 2 -
      ((262144 : ℤ) - t) * ((131071 : ℤ) - t) := by
  rw [shortened_johnson_defect_formula6401]
  omega
theorem shortened_johnson_uniform_listBudget6401
    (t : ℕ) (ht : 150 ≤ t) (_htop : t ≤ 131071) :
    ((262144 : ℤ) - t) *
        (((185354 : ℤ) - t) - ((131071 : ℤ) - t)) ≤
      2765815 *
        (((185354 : ℤ) - t) ^ 2 -
          ((262144 : ℤ) - t) * ((131071 : ℤ) - t)) := by
  rw [shortened_johnson_defect_formula6401]
  omega
theorem shortened_johnson_listBudget_endpoint_exact6401 :
    (261994 : ℤ) * 54283 = 14221820302 ∧
      (185204 : ℤ) ^ 2 - 261994 * 130921 = 5142 ∧
      2765814 * 5142 < 14221820302 ∧
      14221820302 ≤ 2765815 * 5142 := by
  norm_num
noncomputable def scaleGoodSet
    {K ι : Type*} [Field K] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (A : Finset ι) (h : Polynomial K) : Finset ι :=
  A.filter fun i => Polynomial.eval (alpha i) h ≠ 0
theorem scaleGoodSet_card_loss
    {K ι : Type*} [Field K] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (A : Finset ι) (h : Polynomial K) (hh : h ≠ 0) :
    A.card ≤ (scaleGoodSet alpha A h).card + h.natDegree := by
  let bad : Finset ι := A.filter fun i => Polynomial.eval (alpha i) h = 0
  have hbad : bad.card ≤ h.natDegree := by
    by_contra hnot
    have hlt : h.natDegree < bad.card := by omega
    let roots : Finset K := bad.map alpha
    have hz : h = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' h roots
      · intro x hx
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        exact (Finset.mem_filter.mp hi).2
      · rw [Finset.card_map]
        exact hlt
    exact hh hz
  have hpartition := A.card_filter_add_card_filter_not
    (p := fun i => Polynomial.eval (alpha i) h = 0)
  change bad.card + (scaleGoodSet alpha A h).card = A.card at hpartition
  omega
theorem normalized_evaluation_of_fixed_multiplier
    {K ι : Type*} [Field K] [DecidableEq K] [DecidableEq ι]
    (alpha : ι ↪ K) (P₀ h R P : Polynomial K)
    (hfactor : P = P₀ + h * R)
    (i : ι) (hi : Polynomial.eval (alpha i) h ≠ 0) :
    (Polynomial.eval (alpha i) P - Polynomial.eval (alpha i) P₀) /
        Polynomial.eval (alpha i) h =
      Polynomial.eval (alpha i) R := by
  rw [hfactor, Polynomial.eval_add, Polynomial.eval_mul]
  field_simp
  ring
theorem reduces_to_shortened_scaled_baseRS
    {F K ι : Type*} [Field F] [Field K]
    [DecidableEq K] [DecidableEq ι]
    (embed : F →+* K) (beta : ι ↪ F) (alpha : ι ↪ K)
    (halpha : ∀ i, alpha i = embed (beta i))
    (A : Finset ι) (received : ι → K)
    (P₀ h P : Polynomial K) (Rbase : Polynomial F)
    (degreeCap : ℕ)
    (hh : h ≠ 0) (hhdeg : h.natDegree ≤ degreeCap)
    (hP₀deg : P₀.natDegree ≤ degreeCap)
    (hPdeg : P.natDegree ≤ degreeCap)
    (hfactor : P = P₀ + h * Rbase.map embed)
    (howner : ∀ i ∈ A, Polynomial.eval (alpha i) P = received i) :
    A.card ≤ (scaleGoodSet alpha A h).card + h.natDegree ∧
      Rbase.natDegree ≤ degreeCap - h.natDegree ∧
      ∀ i ∈ scaleGoodSet alpha A h,
        embed (Polynomial.eval (beta i) Rbase) =
          (received i - Polynomial.eval (alpha i) P₀) /
            Polynomial.eval (alpha i) h := by
  refine ⟨scaleGoodSet_card_loss alpha A h hh, ?_, ?_⟩
  · have hquot := quotient_natDegree_le_sub h (Rbase.map embed) (P - P₀)
      degreeCap hh hhdeg
      ((Polynomial.natDegree_sub_le P P₀).trans (max_le hPdeg hP₀deg))
      (by rw [hfactor]; ring)
    simpa [Polynomial.natDegree_map embed] using hquot
  · intro i hi
    have hiA := (Finset.mem_filter.mp hi).1
    have hih := (Finset.mem_filter.mp hi).2
    have hnorm := normalized_evaluation_of_fixed_multiplier
      alpha P₀ h (Rbase.map embed) P hfactor i hih
    rw [howner i hiA] at hnorm
    have heval : Polynomial.eval (alpha i) (Rbase.map embed) =
        embed (Polynomial.eval (beta i) Rbase) := by
      simp [halpha i]
    rw [heval] at hnorm
    exact hnorm.symm
def fixedLocatorEmbedding
    {K ι : Type*} [Field K] (sigma : K →+* K)
    (alpha : ι ↪ K) (hfixed : ∀ i, sigma (alpha i) = alpha i) :
    ι ↪ fixedCoefficientField sigma where
  toFun i := ⟨alpha i, hfixed i⟩
  inj' := by
    intro i j hij
    apply alpha.injective
    exact congrArg Subtype.val hij
structure ShortenedScaledBaseRSOwnerData
    {K ι : Type*} [Field K] [DecidableEq K] [DecidableEq ι]
    (sigma : K →+* K) (alpha : ι ↪ K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (A : Finset ι) (received : ι → K)
    (P₀ h P : Polynomial K) (degreeCap : ℕ) where
  Rbase : Polynomial (fixedCoefficientField sigma)
  factorization :
    P = P₀ + h * Rbase.map (fixedCoefficientField sigma).subtype
  degree_bound : Rbase.natDegree ≤ degreeCap - h.natDegree
  agreement_after_shortening :
    agreementSize - h.natDegree ≤ (scaleGoodSet alpha A h).card
  normalized_agreement : ∀ i ∈ scaleGoodSet alpha A h,
    (fixedCoefficientField sigma).subtype
        (Polynomial.eval (fixedLocatorEmbedding sigma alpha hfixed i) Rbase) =
      (received i - Polynomial.eval (alpha i) P₀) /
        Polynomial.eval (alpha i) h
theorem rankOne_family_reduces_to_baseRS_or_smallGenerator6401
    {K J : Type*} [Field K] [DecidableEq K]
    (sigma : K →+* K)
    (alpha : Fin domainSize ↪ K)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (q : BoundedTriple K)
    (hgen : BoundedFixedGenerator sigma (q.2.1 : Polynomial K)
      (q.2.2 : Polynomial K) messageDegree)
    (P₀ : Polynomial K)
    (hP₀deg : P₀.natDegree ≤ messageDegree)
    (hP₀rel : relationPolynomial sigma q P₀ = 0)
    (P : J → Polynomial K)
    (A : J → Finset (Fin domainSize))
    (received : J → Fin domainSize → K)
    (hPdeg : ∀ j, (P j).natDegree ≤ messageDegree)
    (hPrel : ∀ j, relationPolynomial sigma q (P j) = 0)
    (howner : ∀ j, ∀ i ∈ A j,
      Polynomial.eval (alpha i) (P j) = received j i)
    (hAcard : ∀ j, agreementSize ≤ (A j).card) :
    ∃ h : Polynomial K,
      h ≠ 0 ∧
      h.natDegree ≤ messageDegree ∧
      HomogeneousRelation sigma (q.2.1 : Polynomial K)
        (q.2.2 : Polynomial K) h ∧
      (h.natDegree < 150 ∨
        (150 ≤ h.natDegree ∧
          0 < ((agreementSize : ℤ) - h.natDegree) ^ 2 -
            ((domainSize : ℤ) - h.natDegree) *
              ((messageDegree : ℤ) - h.natDegree) ∧
          ((domainSize : ℤ) - h.natDegree) *
              (((agreementSize : ℤ) - h.natDegree) -
                ((messageDegree : ℤ) - h.natDegree)) ≤
            2765815 *
              (((agreementSize : ℤ) - h.natDegree) ^ 2 -
                ((domainSize : ℤ) - h.natDegree) *
                  ((messageDegree : ℤ) - h.natDegree)))) ∧
      ∀ j, Nonempty (ShortenedScaledBaseRSOwnerData sigma alpha hfixed
        (A j) (received j) P₀ h (P j) messageDegree) := by
  obtain ⟨h, hh, hhdeg, hhrel, hgenerate⟩ := hgen
  refine ⟨h, hh, hhdeg, hhrel, ?_, ?_⟩
  · by_cases ht : h.natDegree < 150
    · exact Or.inl ht
    · right
      have ht' : 150 ≤ h.natDegree := by omega
      refine ⟨ht', ?_, ?_⟩
      · simpa [agreementSize, domainSize, messageDegree] using
          shortened_johnson_positive_of_generator_degree_ge150
            h.natDegree ht' hhdeg
      · simpa [agreementSize, domainSize, messageDegree] using
          shortened_johnson_uniform_listBudget6401
            h.natDegree ht' hhdeg
  · intro j
    have hDdeg : (P j - P₀).natDegree ≤ messageDegree :=
      (Polynomial.natDegree_sub_le (P j) P₀).trans
        (max_le (hPdeg j) hP₀deg)
    have hDrel := difference_homogeneous_of_affine_solutions
      sigma q (P j) P₀ (hPrel j) hP₀rel
    obtain ⟨R, hRfixed, hfactor⟩ :=
      hgenerate (P j - P₀) hDdeg hDrel
    obtain ⟨Rbase, hRbase⟩ :=
      fixedPolynomialDescent_to_fixedCoefficientField sigma R hRfixed
    have hfactor' : P j = P₀ +
        h * Rbase.map (fixedCoefficientField sigma).subtype := by
      rw [← hRbase]
      linear_combination hfactor
    have hreduce := reduces_to_shortened_scaled_baseRS
      (fixedCoefficientField sigma).subtype
      (fixedLocatorEmbedding sigma alpha hfixed) alpha
      (fun _ => rfl) (A j) (received j) P₀ h (P j) Rbase
      messageDegree hh hhdeg hP₀deg (hPdeg j) hfactor' (howner j)
    refine ⟨{
      Rbase := Rbase
      factorization := hfactor'
      degree_bound := hreduce.2.1
      agreement_after_shortening := ?_
      normalized_agreement := hreduce.2.2
    }⟩
    exact Nat.sub_le_of_le_add ((hAcard j).trans hreduce.1)
end BCHKSTwoFrobeniusRankOne6401
end ProximityPrize.SubmissionLower
