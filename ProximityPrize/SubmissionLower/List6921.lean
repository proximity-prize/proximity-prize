import ProximityPrize.SubmissionLower.Fast015

set_option Elab.async false
set_option autoImplicit true
set_option maxHeartbeats 1500000
set_option maxRecDepth 100000

namespace List6921

open scoped BigOperators
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42 Astra7

noncomputable section

abbrev ExtraJet := {j : Fin 11 × Fin 22 //
  j.2.val + 2 * j.1.val ≤ 20 ∧ j.2.val + j.1.val ≤ 17}
abbrev SourceJet := Jet ⊕ ExtraJet

def grade : SourceJet → ℕ
  | .inl j => j.1.val
  | .inr _ => 65

def secondExponent : SourceJet → ℕ
  | .inl j => e2 j
  | .inr j => j.val.1.val

def firstExponent : SourceJet → ℕ
  | .inl j => e1 j
  | .inr j => j.val.2.val

def valueExponent (j : SourceJet) : ℕ := grade j - secondExponent j - firstExponent j

def width (j : SourceJet) : ℕ :=
  48 * 180169 - 131072 * grade j + firstExponent j + 2 * secondExponent j

abbrev SourceIndex := (j : SourceJet) × Fin (width j)

def columns (i : SourceIndex) : SourceColumn 2 where
  x := i.2.val
  y₀ := valueExponent i.1
  higher := ![firstExponent i.1, secondExponent i.1]

theorem jet_total (j : SourceJet) : valueExponent j + firstExponent j + secondExponent j = grade j := by
  cases j with
  | inl j => exact Sol1.C42.jet_total j
  | inr j => have hj := j.property.2; simp [valueExponent, grade, firstExponent, secondExponent]; omega

theorem grade_le (j : SourceJet) : grade j ≤ 65 := by
  cases j with
  | inl j => simp [grade]
  | inr j => exact le_rfl

theorem combined_weight (j : SourceJet) : grade j + 4 * (firstExponent j + 2 * secondExponent j) ≤ 148 := by
  cases j with
  | inl j =>
    have hj := j.1.isLt
    have ho := Sol1.C42.jet_order j
    simp only [grade, firstExponent, secondExponent]
    omega
  | inr j => have hj := j.property.1; simp only [grade, firstExponent, secondExponent]; omega

private theorem jet_injective (a b : SourceJet) (hs : grade a = grade b)
    (h1 : firstExponent a = firstExponent b) (h2 : secondExponent a = secondExponent b) : a = b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hgrade : a.1 = b.1 := Fin.ext hs
      obtain ⟨s, c, d⟩ := a
      obtain ⟨t, e, f⟩ := b
      cases hgrade
      have hc : c = e := Fin.ext h2
      cases hc
      exact congrArg (fun d => Sum.inl (⟨s,c,d⟩ : Jet)) (Fin.ext h1)
    | inr b =>
      have ha := a.1.isLt
      simp only [grade] at hs
      omega
  | inr a =>
    cases b with
    | inl b =>
      have hb := b.1.isLt
      simp only [grade] at hs
      omega
    | inr b =>
      exact congrArg Sum.inr (Subtype.ext (Prod.ext (Fin.ext h2) (Fin.ext h1)))

theorem source_weight_lt (i : SourceIndex) :
    i.2.val + 131072 * valueExponent i.1 + 131071 * firstExponent i.1 +
      131070 * secondExponent i.1 < 48 * 180169 := by
  have hs := grade_le i.1
  have ht := jet_total i.1
  have hx := i.2.isLt
  unfold width at hx
  omega

theorem columns_injective : Function.Injective columns := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  have hx := congrArg SourceColumn.x h
  have h0 := congrArg SourceColumn.y₀ h
  have h1 := congrArg (fun c : SourceColumn 2 => c.higher 0) h
  have h2 := congrArg (fun c : SourceColumn 2 => c.higher 1) h
  simp only [columns, Matrix.cons_val_zero, Matrix.cons_val_one] at hx h0 h1 h2
  have ha := jet_total a
  have hb := jet_total b
  have he := jet_injective a b (by omega) h1 h2
  subst b
  exact congrArg (Sigma.mk a) (Fin.ext hx)

theorem columns_y0_le (i : SourceIndex) : (columns i).y₀ ≤ 65 := by
  have ht := jet_total i.1
  have hs := grade_le i.1
  change valueExponent i.1 ≤ 65
  omega

theorem columns_total_le (i : SourceIndex) : totalJetDegree (columns i).exponent ≤ 65 := by
  rw [SourceColumn.totalJetDegree_exponent]
  have ht := jet_total i.1
  have hs := grade_le i.1
  simp [columns, Fin.sum_univ_two]
  omega

theorem columns_weight_lt (i : SourceIndex) :
    Finsupp.weight (differentialWeight 131072) (columns i).exponent < 48 * 180169 := by
  simpa [SourceColumn.weight_exponent, columns, differentialWeight, Fin.sum_univ_two,
    Nat.add_assoc, Nat.mul_comm] using source_weight_lt i

theorem columns_weight148 (i : SourceIndex) :
    Finsupp.weight (jetWeight 1 4 3) (columns i).exponent ≤ 148 := by
  rw [SourceColumn.weight_exponent]
  have ht := jet_total i.1
  have hw := combined_weight i.1
  simp only [columns, jetWeight, Option.elim_none, Option.elim_some, smul_eq_mul,
    mul_zero, zero_add, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.val_zero, Fin.val_one, Fin.val_succ]
  omega

private theorem width_inl (j : Jet) :
    Sol1.C42.width j = width (.inl j) + 4608 := by
  have hs := j.1.isLt
  simp only [Sol1.C42.width, width, grade, firstExponent, secondExponent]
  omega

private theorem extra_total : (∑ j : ExtraJet, width (.inr j)) = 14771159 := by decide +kernel

theorem source_card : Fintype.card SourceIndex = 27294765351 := by
  have htotal := Sol1.C42.source_total
  unfold Sol1.C42.sourceTotal at htotal
  simp_rw [width_inl] at htotal
  rw [Finset.sum_add_distrib] at htotal
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Sol1.C42.jet_count] at htotal
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fintype.sum_sum_type, extra_total]
  have hcombine (s : ℕ) (hs : s + 33149952 = 27313144144) :
      s + 14771159 = 27294765351 := by omega
  exact hcombine _ htotal

theorem strict_source_surplus : 262144 * blockUpper < Fintype.card SourceIndex := by
  rw [source_card, block_upper]
  decide

section Rank

variable {F : Type*} [Field F]

private theorem centered_high_value_zero (center : F) (x a : ℕ) (higher : Fin 2 → ℕ)
    (ha : 48 ≤ a) :
    localConstraintCoordinatesAt 48 center 0 (sourceMonomial (R := F) x a higher) = 0 := by
  have hdiv : (MvPolynomial.X (some 0) : DifferentialPolynomial F 2) ^ a ∣ sourceMonomial x a higher := by
    unfold sourceMonomial
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hmap := map_dvd (unscaledLocalSubstitution 2 center 0).toRingHom hdiv
  change unscaledLocalSubstitution 2 center 0 ((MvPolynomial.X (some 0)) ^ a) ∣
    unscaledLocalSubstitution 2 center 0 (sourceMonomial x a higher) at hmap
  rw [map_pow, unscaledLocalSubstitution_Y_zero, MvPolynomial.C_0, zero_add, ← T_mul_localJetSum, ← mul_add] at hmap
  obtain ⟨G,hG⟩ := hmap
  have hz : localConstraintAt (R := F) (d := 2) 48 center 0
      (sourceMonomial x a higher) = 0 := by
    rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      projectLowContact, weightedTruncation_eq_zero_iff, hG, mul_pow, mul_assoc]
    have hT := pow_mem_restrictWeightedOrder (R := F)
      (X_mem_restrictWeightedOrder (localContactWeight 2) (localT 2) le_rfl) a
    have hrest : (localJetSum (R := F) 2 + MvPolynomial.X (localE 2)) ^ a * G ∈
        restrictWeightedOrder (localContactWeight 2) 0 := by simp
    refine restrictWeightedOrder_anti _ ?_ (mul_mem_restrictWeightedOrder hT hrest)
    simpa only [localContactWeight_T, add_zero, one_mul, mul_one] using ha
  exact (satisfiesLocalConstraints_iff_coordinates_eq_zero 48 center 0
    (sourceMonomial x a higher)).mp hz

private theorem old_matrix_span (center received : F) (Q : DifferentialPolynomial F 2)
    (hQ : Q ∈ sourceSpan F) :
    localConstraintCoordinatesAt 48 center received Q ∈
      Submodule.span F (Set.range (pointMatrix (F := F) 48 0 0).col) := by
  let L := localConstraintCoordinatesAt (R := F) (d := 2) 48 0 0
  have hmap : (sourceSpan F).map L =
      Submodule.span F (Set.range (pointMatrix (F := F) 48 0 0).col) := by
    rw [sourceSpan, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← hmap, coordinates_translation]
  exact ⟨_, sourceSpan_translation center received Q hQ, rfl⟩

private theorem value_translation_sourceMonomial (received : F) (x a : ℕ) (higher : Fin 2 → ℕ) :
    globalPointTranslation (0 : F) received (sourceMonomial x a higher) =
      ∑ k ∈ Finset.range (a + 1),
        (received ^ (a - k) * (a.choose k : F)) • sourceMonomial x k higher := by
  unfold sourceMonomial
  simp only [map_mul, map_pow, map_prod, globalPointTranslation_X,
    globalPointTranslation_Y_zero, globalPointTranslation_Y_succ, MvPolynomial.C_0, zero_add]
  rw [add_comm (MvPolynomial.C received), add_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, map_pow, map_natCast]
  ring

private theorem sourceMonomial_mem_old (x a b c : ℕ) (h : Eligible x a b c) :
    sourceMonomial (R := F) x a ![b,c] ∈ sourceSpan F := by
  obtain ⟨i, hi⟩ := index_of_eligible x a b c h
  have hh : ((Sol1.C42.columns i).polynomial : DifferentialPolynomial F 2) ∈ sourceSpan F :=
    Submodule.subset_span ⟨i,rfl⟩
  rwa [SourceColumn.polynomial_eq_sourceMonomial, hi] at hh

private theorem column_mem_old_matrix_span (center received : F) (i : SourceIndex) :
    localConstraintCoordinatesAt 48 center received ((columns i).polynomial) ∈
      Submodule.span F (Set.range (pointMatrix (F := F) 48 0 0).col) := by
  obtain ⟨j, x⟩ := i
  have hw := source_weight_lt ⟨j,x⟩
  cases j with
  | inl j =>
    have h := Sol1.C42.jet_total j
    have hdeg := j.1.isLt
    have ho := Sol1.C42.jet_order j
    rw [SourceColumn.polynomial_eq_sourceMonomial]
    apply old_matrix_span
    apply sourceMonomial_mem_old
    simp only [Eligible, columns, valueExponent, grade, firstExponent, secondExponent] at *
    change e0 j + e1 j + e2 j = j.1.val at h
    simp only [e0] at h
    omega
  | inr j =>
    have hdeg := j.property.2
    have ho := j.property.1
    rw [SourceColumn.polynomial_eq_sourceMonomial]
    have htranslation (Q : DifferentialPolynomial F 2) :
        localConstraintCoordinatesAt 48 center received Q =
          localConstraintCoordinatesAt 48 center 0 (globalPointTranslation 0 received Q) := by
      rw [coordinates_translation 48 center received, coordinates_translation 48 center 0]
      congr 1
      change globalPointTranslation center received Q =
        ((globalPointTranslation center 0).comp (globalPointTranslation 0 received)) Q
      rw [globalPointTranslation_comp, zero_add, add_zero]
    rw [htranslation, value_translation_sourceMonomial, map_sum]
    apply Submodule.sum_mem
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [map_smul]
    apply Submodule.smul_mem
    by_cases he : k = (columns (⟨Sum.inr j,x⟩ : SourceIndex)).y₀
    · rw [he, centered_high_value_zero]
      · exact Submodule.zero_mem _
      · simp only [columns, valueExponent, grade, firstExponent, secondExponent]
        omega
    · apply old_matrix_span
      apply sourceMonomial_mem_old
      simp only [Eligible, columns, valueExponent, grade, firstExponent, secondExponent] at *
      omega

private theorem rank_le_old (center received : F) :
    (Matrix.rank (fun row j ↦ localConstraintCoordinatesAt 48 center received (columns j).polynomial row :
      Matrix (LowContactIndex 2 48) SourceIndex F)) ≤ blockUpper := by
  classical
  let M : Matrix (LowContactIndex 2 48) SourceIndex F :=
    fun row j ↦ localConstraintCoordinatesAt 48 center received (columns j).polynomial row
  have hspan : Submodule.span F (Set.range M.col) ≤
      Submodule.span F (Set.range (pointMatrix (F := F) 48 0 0).col) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact column_mem_old_matrix_span center received i
  refine le_trans ?_ (Sol1.C52.origin_rank (F := F))
  change M.rank ≤ _
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  have := FiniteDimensional.span_of_finite (K := F)
    (Set.finite_range (pointMatrix (F := F) 48 0 0).col)
  exact Submodule.finrank_mono hspan

end Rank

private theorem constraint_matrix_map {R S : Type*} [CommRing R] [CommRing S]
    (phi : R →+* S) (centers received : Fin 262144 → R) :
    (localConstraintMatrix 48 centers received columns).map phi =
      localConstraintMatrix 48 (fun i => phi (centers i)) (fun i => phi (received i)) columns := by
  ext row j
  simp only [Matrix.map_apply, localConstraintMatrix_apply]
  rw [← MvPolynomial.coeff_map, map_unscaledLocalSubstitution]
  simp [SourceColumn.polynomial]

private theorem rank_sum_const (n bound : ℕ) : (∑ _i : Fin n, bound) = n * bound := by
  simp

private theorem global_rank_le {R F : Type*} [CommRing R] [Field F]
    (centers received : Fin 262144 → R) (phi : R →+* F) :
    ((localConstraintMatrix 48 centers received columns).map phi).rank ≤ 262144 * blockUpper := by
  classical
  rw [constraint_matrix_map]
  apply (Matrix.rank_prod_rows_le_sum _).trans
  calc
    (∑ i : Fin 262144, Matrix.rank (fun row j =>
      localConstraintMatrix 48 (fun k => phi (centers k))
        (fun k => phi (received k)) columns (i,row) j)) ≤
        ∑ _i : Fin 262144, blockUpper := by
      apply Finset.sum_le_sum
      intro i _
      exact rank_le_old (phi (centers i)) (phi (received i))
    _ = 262144 * blockUpper := rank_sum_const 262144 blockUpper

universe u
attribute [local instance] Classical.propDecidable


theorem extended_uniform_annihilator {F : Type u} [Field F]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    ∃ Q : DifferentialPolynomial F 2, Q ≠ 0 ∧ jetTotalDegree Q ≤ 65 ∧
      Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148 ∧
      ∀ P ∈ ReedSolomon.closePolynomialSet domain received 131073 180169,
        differentialSpecialization Q P=0 := by
  classical
  let K := FractionRing (Polynomial F)
  let phi : Polynomial F →+* K := algebraMap (Polynomial F) K
  have hphi : Function.Injective phi := IsFractionRing.injective (Polynomial F) K
  have hrank : ((localConstraintMatrix 48 (fun i => Polynomial.C (domain i))
      (fun i => Polynomial.C (received i)) columns).map phi).rank ≤ 262144 * blockUpper :=
    global_rank_le (fun i => Polynomial.C (domain i)) (fun i => Polynomial.C (received i)) phi
  obtain ⟨v,_,hvdegree,hspan,_,hconstraints⟩ :=
    exists_primitive_interpolant_of_rank_le.{u,0,0,u,u} 48 0 65 (fun i => domain i)
      (fun i => Polynomial.C (received i)) (by intro i; simp) columns
      columns_injective columns_y0_le phi hphi hrank strict_source_surplus
  let Qs : DifferentialPolynomial (Polynomial F) 2 := SourceColumn.interpolant columns v
  let psi : Polynomial F →+* F := Polynomial.evalRingHom 0
  let Q : DifferentialPolynomial F 2 := MvPolynomial.map psi Qs
  have hQ0 : Q ≠ 0 := by
    exact SourceColumn.map_interpolant_ne_zero columns_injective psi
      (Ideal.comp_ne_zero_of_span_range_eq_top hspan psi)
  have hjet : jetTotalDegree Q ≤ 65 :=
    SourceColumn.map_interpolant_jetTotalDegree_le psi columns columns_total_le v
  have hwt : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148 :=
    generic_source_weight_le psi columns v (jetWeight 1 4 3) 148 columns_weight148
  refine ⟨Q,hQ0,hjet,hwt,?_⟩
  intro P hP
  have hPdegree : P.natDegree ≤ 131072 := by
    by_cases hz : P=0
    · simp [hz]
    · have hh := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP.1
      omega
  have hQweight : differentialWeightedDegree 131072 Q < 48*180169 :=
    generic_source_weight_lt psi columns v (differentialWeight 131072) (48*180169)
      (by decide) columns_weight_lt
  have hlocal : ∀ i, SatisfiesLocalConstraints 48 (domain i) (received i) Q := by
    intro i
    have hh := SatisfiesLocalConstraints.map psi 48 (Polynomial.C (domain i))
      (Polynomial.C (received i)) Qs (hconstraints i)
    simpa [psi,Q] using hh
  let indices := ReedSolomon.polynomialAgreementSet domain received P
  apply differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    domain received indices hQweight (fun i _ => hlocal i) P hPdegree
    domain.injective.injOn hP.2
  intro i hi
  exact (Finset.mem_filter.mp hi).2

end
end List6921

namespace List6921

open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative MvPolynomial
open Sol1.C42 Sol1.C57 Astra7

noncomputable section
variable {F E : Type*} [Field F] [Field E] [CharP E 2130706433]

def I1 : ℚ := 131072 / 49097
def firstOrderCharge (h : ℕ) : ℚ := I1 * h * b h + (h : ℚ) * (h - 1)

def weightedRegularCap : ℚ := (148 : ℚ) / 45 *
  (((131072 : ℚ)*36962583)/49097)^2

private theorem characteristic_not_dvd_weight (j : Fin 3) :
    ¬ 2130706433 ∣ 1 + 4 * j.val := by
  apply Nat.not_dvd_of_pos_of_lt
  · positivity
  · have hj := j.isLt
    omega

theorem weighted_regular_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2)
    (hQ : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148)
    (S : Finset (Polynomial F))
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last 2)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180169) :
    (S.card : ℚ) ≤ weightedRegularCap := by
  classical
  have hchar : ∀ j : Fin 3, ((1+4*j.val : ℕ) : F) ≠ 0 := by
    intro j hz
    exact characteristic_not_dvd_weight j
      ((CharP.cast_eq_zero_iff F 2130706433 (1 + 4 * j.val)).mp hz)
  have hh := weighted_regular_polynomial_card (r := 2) (n := 262144) (k := 131073) (A := 180169)
    1 4 148 (by decide) (by decide) hchar Q hQ
    (by decide) (by decide) domain received Astra7.native_choose_two S
    (fun P hP => (hS P hP).2.1) (fun P hP => (hS P hP).1) hsep
    (fun P hP => (hS P hP).2.2)
  norm_num [chartBound,Fin.prod_univ_succ] at hh
  dsimp [weightedRegularCap]
  linarith


theorem regular_top_card_le_at_agreement (d : ℕ) (hd : d ≤ 2)
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E d) (nu : ℕ)
    (hhighest : highestActiveJet Q = some (Fin.last d)) (hweight : jetTotalDegree Q ≤ nu)
    (S : Finset E[X])
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last d)) P ≠ 0)
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180169) :
    (S.card : ℚ) ≤ dimensionSensitiveIncidenceProduct 262144 180169 131073 1 d * nu *
      ((1 + 2 * 131073 * (nu - 1) : ℕ) : ℚ) ^ d := by
  have hactual := finite_actualStage_regularSolutions_card_le_dimensionSensitive Q (Fin.last d)
    hhighest 131073 131073 (by omega) le_rfl domain received (by norm_num) (by norm_num)
    (fun r hr ↦ Sol1.C40Primitives.native_binomial_guard r (hr.trans hd)) S hsep hS
  exact hactual.trans (directJetStageCharge_le_weight_order (Q, Fin.last d)
    262144 180169 131073 131073 nu d (by norm_num) hweight (by simp))
theorem incidence_one : dimensionSensitiveIncidenceProduct 262144 180169 131073 1 1 = I1 := by
  norm_num [dimensionSensitiveIncidenceProduct, I1]
theorem firstOrderCharge_ge (h : ℕ) : (h : ℚ) ≤ firstOrderCharge h := by
  have hi : (1 : ℚ) ≤ I1 := by norm_num [I1]
  have hI : 0 ≤ I1 := by norm_num [I1]
  have hb : (1 : ℚ) ≤ (b h : ℚ) := by
    exact_mod_cast (by unfold b; omega : 1 ≤ b h)
  have hprod : 0 ≤ (h : ℚ) * (h - 1) := by
    rw [← Sol1.C57.cast_mul_pred]
    positivity
  have h1 : (h : ℚ) ≤ I1 * h := by nlinarith [Nat.cast_nonneg (α := ℚ) h]
  have h2 : I1 * h ≤ I1 * h * b h :=
    le_mul_of_one_le_right (mul_nonneg hI (Nat.cast_nonneg _)) hb
  exact (h1.trans h2).trans (le_add_of_nonneg_right hprod)

/-- Sharp whole first-order fixed-word consumer, including every singular/lower-order root. -/
theorem first_order_card_le_at_agreement
    (domain : Fin 262144 ↪ E) (received : Fin 262144 → E)
    (Q : DifferentialPolynomial E 1) (hQ : Q ≠ 0) (h : ℕ) (hbound : h < 2130706433)
    (hweight : jetTotalDegree Q ≤ h) (S : Finset E[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180169) :
    (S.card : ℚ) ≤ firstOrderCharge h := by
  classical
  let G := regularPart 0 Q
  have hsplit := split_weight 0 Q
  have hGweight : jetTotalDegree G ≤ h := by dsimp [G]; omega
  have hchar : ringChar E = 0 ∨ jetDegree Q (Fin.last 1) < ringChar E := by
    right
    rw [ringChar.eq E 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 1)
    omega
  by_cases hb : jetDegree G (Fin.last 1) = 0
  · have hGone : G = 1 := regular_eq_one_of_degree_zero 0 Q hb
    have hlow : ∀ P ∈ S, differentialSpecialization (lowerPart 0 Q) P = 0 := by
      intro P hP
      rcases root_split 0 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P = 0 at hr
        rw [hGone] at hr
        have hz : (1 : E[X]) = 0 := by
          simpa only [differentialSpecialization, map_one] using hr
        exact (one_ne_zero hz).elim
    have hc := order_zero_card_le (lowerPart 0 Q) (lower_ne_zero 0 Q) S hlow
    have hch : S.card ≤ h := by omega
    exact (by exact_mod_cast hch : (S.card : ℚ) ≤ h).trans (firstOrderCharge_ge h)
  · have hbpos : 0 < jetDegree G (Fin.last 1) := by omega
    let good : E[X] → Prop := fun P ↦ differentialSpecialization G P = 0 ∧
      differentialSpecialization (separant G (Fin.last 1)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P ↦ ¬ good P
    have hreg : (regular.card : ℚ) ≤ I1 * h * b h := by
      have hx := regular_top_card_le_at_agreement 1 (by norm_num) domain received G h
        (highestActiveJet_last_of_pos G hbpos) hGweight regular
        (by intro P hP; exact ((Finset.mem_filter.mp hP).2).2)
        (by
          intro P hP
          have hp := Finset.mem_filter.mp hP
          exact ⟨hp.2.1,(hS P hp.1).2⟩)
      simpa only [incidence_one, pow_one, b] using hx
    let R := exceptionalEquation 0 Q
    have hR : R ≠ 0 := exceptional_ne_zero 0 Q hchar
    have hRweight : jetTotalDegree R ≤ h * (h - 1) :=
      exceptional_weight_sharp 0 Q h hweight
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 1)))
    have hexc : exceptional.card ≤ h * (h - 1) := by
      apply (order_zero_card_le R hR exceptional ?_).trans hRweight
      intro P hP
      have hp := Finset.mem_filter.mp hP
      rcases root_regular_or_exceptional 0 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hcard : regular.card + exceptional.card = S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ) = (regular.card : ℚ) + exceptional.card := by exact_mod_cast hcard.symm
      _ ≤ I1 * h * b h + ((h * (h - 1) : ℕ) : ℚ) :=
        add_le_add hreg (by exact_mod_cast hexc)
      _ = firstOrderCharge h := by rw [Sol1.C57.cast_mul_pred]; rfl
def weightedFullCharge : ℚ := weightedRegularCap + firstOrderCharge 4160
def weightedListCap : ℕ := 32036712204253056

theorem weighted_budget_exact : weightedFullCharge ≤ weightedListCap := by
  norm_num [weightedFullCharge, weightedRegularCap, firstOrderCharge, I1, b, weightedListCap]

theorem weighted_second_order_card [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F)
    (Q : DifferentialPolynomial F 2) (hQ : Q ≠ 0) (hjet : jetTotalDegree Q ≤ 65)
    (hwt : Q.weightedTotalDegree (jetWeight 1 4 3) ≤ 148)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P ∈ directJetAgreementSolutions Q domain received 131073 180169) :
    (S.card : ℚ) ≤ weightedFullCharge := by
  classical
  let G := regularPart 1 Q
  have hsplit := split_weight 1 Q
  have hGjet : jetTotalDegree G ≤ 65 := by dsimp [G]; omega
  have hGwt : G.weightedTotalDegree (jetWeight 1 4 3) ≤ 148 :=
    (weightedTotalDegree_le_of_dvd (jetWeight 1 4 3) (Astra7.regularPart_dvd 1 Q) hQ).trans hwt
  have hchar : ringChar F=0 ∨ jetDegree Q (Fin.last 2) < ringChar F := by
    right
    rw [ringChar.eq F 2130706433]
    have hh := jetDegree_le_total Q (Fin.last 2)
    omega
  have hcost : 0 ≤ weightedRegularCap := by unfold weightedRegularCap; positivity
  by_cases hb : jetDegree G (Fin.last 2)=0
  · have hGone : G=1 := regular_eq_one_of_degree_zero 1 Q hb
    have hlow : ∀ P ∈ S, P ∈ directJetAgreementSolutions (lowerPart 1 Q)
        domain received 131073 180169 := by
      intro P hP
      refine ⟨?_,(hS P hP).2⟩
      rcases root_split 1 Q hQ P (hS P hP).1 with hc | hr
      · exact hc
      · change differentialSpecialization G P=0 at hr
        rw [hGone] at hr
        have hz : (1 : F[X])=0 := by
          simpa only [differentialSpecialization,map_one] using hr
        exact (one_ne_zero hz).elim
    have hlowjet : jetTotalDegree (lowerPart 1 Q) ≤ 4160 := by omega
    have hc := first_order_card_le_at_agreement domain received (lowerPart 1 Q) (lower_ne_zero 1 Q)
      4160 (by decide) hlowjet S hlow
    exact hc.trans (le_add_of_nonneg_left hcost)
  · have hbpos : 0 < jetDegree G (Fin.last 2) := by omega
    let good : F[X] → Prop := fun P => differentialSpecialization G P=0 ∧
      differentialSpecialization (separant G (Fin.last 2)) P ≠ 0
    let regular := S.filter good
    let exceptional := S.filter fun P => ¬good P
    have hr : (regular.card : ℚ) ≤ weightedRegularCap := by
      apply weighted_regular_card domain received G hGwt regular
      · intro P hP
        exact ((Finset.mem_filter.mp hP).2).2
      · intro P hP
        have hp := Finset.mem_filter.mp hP
        exact ⟨hp.2.1,(hS P hp.1).2⟩
    let R := exceptionalEquation 1 Q
    have hR : R ≠ 0 := exceptional_ne_zero 1 Q hchar
    have hRjet : jetTotalDegree R ≤ 4160 := by
      have hh := exceptional_weight_sharp 1 Q 65 hjet
        (hbpos.trans_le (jetDegree_le_total G (Fin.last 2)))
      exact hh
    have he : (exceptional.card : ℚ) ≤ firstOrderCharge 4160 := by
      apply first_order_card_le_at_agreement domain received R hR 4160 (by decide) hRjet exceptional
      intro P hP
      have hp := Finset.mem_filter.mp hP
      refine ⟨?_,(hS P hp.1).2⟩
      rcases root_regular_or_exceptional 1 Q hQ P (hS P hp.1).1 hbpos with hg | he
      · exact (hp.2 hg).elim
      · exact he
    have hc : regular.card+exceptional.card=S.card :=
      Finset.card_filter_add_card_filter_not (s := S) (p := good)
    calc
      (S.card : ℚ)=(regular.card : ℚ)+exceptional.card := by exact_mod_cast hc.symm
      _ ≤ weightedRegularCap+firstOrderCharge 4160 := add_le_add hr he
      _ = weightedFullCharge := rfl

attribute [local instance] Classical.propDecidable

theorem weighted_complete_list [CharP F 2130706433]
    (domain : Fin 262144 ↪ F) (received : Fin 262144 → F) :
    (ReedSolomon.closePolynomialSet domain received 131073 180169).Finite ∧
      (ReedSolomon.closePolynomialSet domain received 131073 180169).ncard ≤ weightedListCap := by
  classical
  obtain ⟨Q,hQ,hjet,hwt,hsound⟩ := extended_uniform_annihilator domain received
  have hf : ∀ S : Finset F[X],
      (S : Set F[X]) ⊆ ReedSolomon.closePolynomialSet domain received 131073 180169 →
      S.card ≤ weightedListCap := by
    intro S hS
    have hh := weighted_second_order_card domain received Q hQ hjet hwt S
      (fun P hP => ⟨hsound P (hS hP),hS hP⟩)
    exact_mod_cast hh.trans weighted_budget_exact
  have hfin : (ReedSolomon.closePolynomialSet domain received 131073 180169).Finite := by
    by_contra hi
    obtain ⟨S,hS,hcard⟩ := Set.Infinite.exists_subset_card_eq hi (weightedListCap+1)
    have hh := hf S hS
    omega
  refine ⟨hfin,?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hf hfin.toFinset (fun P hP => hfin.mem_toFinset.mp hP)

local instance : DecidableEq Sol1.C42.NativeK := Classical.decEq _

theorem native_weighted_complete_list (received : Sol1.C42.NativeIndex → Sol1.C42.NativeK) :
    (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180169).Finite ∧
      (ReedSolomon.closePolynomialSet ProximityPrize.Benchmark.IRSProfile.domain received 131073 180169).ncard ≤
        weightedListCap := by
  let := Sol1.C42.native_charP
  exact weighted_complete_list ProximityPrize.Benchmark.IRSProfile.domain received

end
end List6921

namespace List6921.Native
noncomputable section
open Polynomial Code LinearCode CoreDefinitions
open ProximityPrize.Benchmark Sol1.OneCount Sol1.FiniteRowProjection Sol1.C42
set_option maxRecDepth 10000
set_option maxHeartbeats 0

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq A16 := Classical.decEq A16

def radius6921 : ℝ := (335773130 : ℝ) / 1073741824

/-- Original scalar RS words lie in the proved augmented ordinary polynomial list. -/
theorem finset_scalar_list_card_le (w : I → K) (P : Finset (I → K))
    (hP : ∀ f ∈ P, f ∈ scalarCode ∧ 180169 ≤ agreementCard f w) : P.card ≤ List6921.weightedListCap := by
  classical
  have : NeZero (131072 : ℕ) := ⟨by norm_num⟩
  choose poly hdegree heval using fun f : P ↦
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp (hP f.val f.property).1
  have hinj : Function.Injective poly := by
    intro f g hfg
    apply Subtype.ext
    funext i
    calc
      f.val i = (poly f).eval (IRSProfile.domain i) := (heval f i).symm
      _ = (poly g).eval (IRSProfile.domain i) := by rw [hfg]
      _ = g.val i := heval g i
  let polys : Finset K[X] := Finset.univ.image poly
  have hpolyscard : polys.card = P.card := by
    dsimp [polys]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hpolys : (polys : Set K[X]) ⊆
      ReedSolomon.closePolynomialSet IRSProfile.domain w 131073 180169 := by
    intro q hq
    obtain ⟨f,_hf,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨?_, ?_⟩
    · have hd : (poly f).natDegree < 131073 := (hdegree f).trans (by norm_num)
      exact (Polynomial.degree_le_natDegree).trans_lt (by exact_mod_cast hd)
    · have hword : (fun i ↦ (poly f).eval (IRSProfile.domain i)) = f.val := funext (heval f)
      change 180169 ≤ agreementCard (fun i ↦ (poly f).eval (IRSProfile.domain i)) w
      rw [hword]
      exact (hP f.val f.property).2
  obtain ⟨hfinite,hbound⟩ := List6921.native_weighted_complete_list w
  have hcount := (Set.ncard_le_ncard hpolys hfinite).trans hbound
  have hcount' : polys.card ≤ List6921.weightedListCap := by simpa only [Set.ncard_coe_finset] using hcount
  rwa [hpolyscard] at hcount'

theorem list_projection_room : (List6921.weightedListCap + 1) ^ 2 ≤ Fintype.card K :=
  projection_room List6921.weightedListCap (by norm_num [List6921.weightedListCap])

/-- The actual alphabet is Fin2 -> Fin8 -> K; flattening only reindexes its rows. -/
theorem finset_squared_list_card_le (w : I → A16) (P : Finset (I → A16))
    (hP : ∀ f ∈ P, f ∈ squaredCode ∧ 180169 ≤ agreementCard f w) : P.card ≤ List6921.weightedListCap := by
  classical
  let flattened := P.image flatten
  have hflat : ∀ f ∈ flattened,
      (∀ r : R16, (fun i ↦ f i r) ∈ scalarCode) ∧
        180169 ≤ agreementCard f (flatten w) := by
    intro f hf
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hcode,hagree⟩ := hP g hg
    exact ⟨flatten_rows_mem g hcode,hagree.trans (flatten_agreement_le g w)⟩
  have hcount := finset_vector_list_card_le scalarCode 180169 List6921.weightedListCap list_projection_room
    finset_scalar_list_card_le (flatten w) flattened hflat
  have hcard : flattened.card = P.card := Finset.card_image_of_injective P flatten_injective
  rwa [hcard] at hcount

theorem close_agreement_ge (f w : I → A16)
    (hd : (δᵣ(w,f) : ℝ) ≤ radius6921) : 180169 ≤ agreementCard f w := by
  classical
  have hpos : 0 < Fintype.card I := by norm_num [I,IRSProfile.Index]
  have hradius : radius6921 = 1 - ((368984347 : ℝ) / 2048) / Fintype.card I := by
    norm_num [radius6921,I,IRSProfile.Index]
  have hagree : (368984347 : ℝ) / 2048 ≤ Code.agree f w :=
    (Code.relHammingDist_le_one_sub_div_iff hpos).mp (by rwa [← hradius])
  have hstrict : (180168 : ℝ) < Code.agree f w :=
    (by norm_num : (180168 : ℝ) < (368984347 : ℝ) / 2048).trans_le hagree
  have hnat : 180168 < agreementCard f w := by exact_mod_cast hstrict
  omega

/-- Actual maximized independent IRS16 list term, with no MCA or list hypothesis. -/
theorem squared_lambda_le :
    Code.Lambda (squaredCode : Set (I → A16)) radius6921 ≤ (List6921.weightedListCap : ℕ∞) := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro w
  have hfinite : (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6921).Finite :=
    Set.toFinite _
  have hcard : hfinite.toFinset.card ≤ List6921.weightedListCap := by
    apply finset_squared_list_card_le w hfinite.toFinset
    intro f hf
    obtain ⟨hcode,hclose⟩ := Code.mem_closeCodewordsRel_iff.mp (hfinite.mem_toFinset.mp hf)
    exact ⟨hcode,close_agreement_ge f w hclose⟩
  calc
    (Code.closeCodewordsRel (squaredCode : Set (I → A16)) w radius6921).encard =
        (hfinite.toFinset.card : ℕ∞) := hfinite.encard_eq_coe_toFinset_card
    _ ≤ (List6921.weightedListCap : ℕ∞) := by exact_mod_cast hcard

/-- Expanded actual-code benchmark form. -/
theorem actual_squared_lambda_le :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) : ModuleCode I K A16) : Set (I → A16)) radius6921 ≤ (List6921.weightedListCap : ℕ∞) := squared_lambda_le

end
end List6921.Native
