import ProximityPrize.SubmissionLower.Fast077

set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace Low48BentCycle

noncomputable section

open K1_13_6 K1_13_6_2 MvPolynomial
open K1_13_6_2_4 (Exponent OfDim DimLE Component LengthAt sectionIdeal dim_le_after_section)
open K1_13_6_2_4_1 (Grade Form unitGrade squarefree slotWeight piece gradedHilbert
  Represents TopNonnegative line positiveDiagonal component_mul_of_grade homogeneous_cut_exact
  forms_of_counts eq_sub_previous backwardDiff previous backwardDiff_degree_le previous_degree_le
  squarefree_degree backwardDiff_coeff_squarefree previous_coeff line_eval totalDegree_le_of_lines
  cube_extract positiveDiagonal_apply)
open scoped BigOperators Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra

abbrev Family := Fin 5 → Set Exponent

def diagonalExponents (B : Family) (t : Grade) : Set Exponent :=
  {m | ∃ u : (i : Fin 5) → Fin (t i) → Exponent,
    (∀ i j, u i j ∈ B i) ∧ m = ∑ i, ∑ j, u i j}

instance diagonalExponentsFinite (B : Family) [∀ i, Finite (B i)] (t : Grade) :
    Finite (diagonalExponents B t) := by
  let addExponents (u : (i : Fin 5) → Fin (t i) → B i) : Exponent :=
    ∑ i, ∑ j, (u i j).val
  have heq : diagonalExponents B t = Set.range addExponents := by
    ext m
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i j => ⟨u i j, hu i j⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨fun i j => (u i j).val, fun i j => (u i j).property, rfl⟩
  rw [heq]
  exact (Set.finite_range _).to_subtype
def mixedDegree (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (I : Finset (Fin 5)) : ℚ :=
  (∑ J ∈ I.powerset, (-1 : ℚ) ^ (I.card - J.card) *
    (MvPolynomial.affineHilbertPolynomial (Ideal.comap
      (MvPolynomial.monomialMap GeoField (diagonalExponents B (positiveDiagonal J)))
      P)).coeff I.card) / (2 : ℚ) ^ I.card
abbrev Generator (B : Family) := (i : Fin 5) × B i
abbrev SlotRing (B : Family) := MvPolynomial (Generator B) GeoField
instance (B : Family) [∀ i, Finite (B i)] : Finite (Generator B) := by
  infer_instance

def slot (B : Family) : Generator B → Fin 5 := Sigma.fst
def taggedMap (B : Family) : SlotRing B →ₐ[GeoField] GeoJets5 :=
  aeval fun v => monomial v.2.val 1
def gradedIdeal (B : Family) (P : Ideal GeoJets5) : Ideal (SlotRing B) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).toIdeal
def diagonalIdeal (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (t : Grade) :=
  P.comap (monomialMap GeoField (diagonalExponents B t))
theorem gradedIdeal_homogeneous (B : Family) (P : Ideal GeoJets5) :
    (gradedIdeal B P).IsHomogeneous (piece (slot B)) :=
  ((P.comap (taggedMap B)).homogeneousCore (piece (slot B))).isHomogeneous
theorem gradedIdeal_mono (B : Family) {P Q : Ideal GeoJets5} (h : P ≤ Q) :
    gradedIdeal B P ≤ gradedIdeal B Q :=
  Ideal.homogeneousCore_mono _ (Ideal.comap_mono h)
theorem mem_gradedIdeal_of_grade {B : Family} {P : Ideal GeoJets5} {a : SlotRing B}
    {t : Grade} (ha : a ∈ piece (slot B) t) :
    a ∈ gradedIdeal B P ↔ taggedMap B a ∈ P := by
  constructor
  · intro h
    exact Ideal.toIdeal_homogeneousCore_le (piece (slot B)) (P.comap (taggedMap B)) h
  · intro h
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨t, ha⟩ h
open K1_13_6_2_4_1 (homogeneous_colon regular_colon square_colon)

private theorem gradedIdeal_colon {B : Family} {P Q : Ideal GeoJets5} {g : SlotRing B}
    {e : Grade} (hg : g ∈ piece (slot B) e)
    (h : ∀ a : GeoJets5, a * taggedMap B g ∈ P ↔ a ∈ Q) :
    (gradedIdeal B P).colon {g} = gradedIdeal B Q := by
  ext a
  rw [mem_iff_weightedHomogeneousComponent_mem _ _
      (homogeneous_colon (slot B) (gradedIdeal_homogeneous B P) hg),
    mem_iff_weightedHomogeneousComponent_mem _ _ (gradedIdeal_homogeneous B Q)]
  apply forall_congr'
  intro t
  let z := weightedHomogeneousComponent (slotWeight (slot B)) t a
  have hz : z ∈ piece (slot B) t := weightedHomogeneousComponent_mem _ _ _
  have hg' : g.IsWeightedHomogeneous (slotWeight (slot B)) e := hg
  have hzg : z * g ∈ piece (slot B) (t + e) :=
    (weightedHomogeneousComponent_isWeightedHomogeneous t a).mul hg'
  change z ∈ (gradedIdeal B P).colon {g} ↔ z ∈ gradedIdeal B Q
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mem_gradedIdeal_of_grade hzg,
    mem_gradedIdeal_of_grade hz, map_mul, h]
private theorem exists_slot_lift (B : Family) (i : Fin 5) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ B i) :
    ∃ g : SlotRing B, g ∈ piece (slot B) (unitGrade i) ∧ taggedMap B g = D := by
  classical
  let gen (m : D.support) : Generator B := ⟨i, ⟨m, hD m m.property⟩⟩
  refine ⟨∑ m : D.support, C (D.coeff m) * MvPolynomial.X (gen m), ?_, ?_⟩
  · apply Submodule.sum_mem
    intro m _
    have hc : (C (D.coeff m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) 0 :=
      isWeightedHomogeneous_C _ _
    have hx : (MvPolynomial.X (gen m) : SlotRing B).IsWeightedHomogeneous (slotWeight (slot B)) (unitGrade i) :=
      isWeightedHomogeneous_X GeoField (slotWeight (slot B)) (gen m)
    rw [mem_weightedHomogeneousSubmodule]
    simpa only [zero_add] using hc.mul hx
  · simp only [map_sum, map_mul, taggedMap, aeval_C, algebraMap_eq, aeval_X,
      C_mul_monomial, mul_one, gen]
    rw [Finset.sum_coe_sort D.support (fun m => monomial m (D.coeff m))]
    exact D.support_sum_monomial_coeff
theorem exists_regular_lifts (B : Family) (P : Ideal GeoJets5) (i : Fin 5) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ B i)
    (hD₂ : ∀ m ∈ (D ^ 2).support, m ∈ B i) (hr : IsLeftRegular (Ideal.Quotient.mk P D)) :
    ∃ f g : SlotRing B,
      f ∈ piece (slot B) (unitGrade i) ∧ g ∈ piece (slot B) (unitGrade i) ∧
      (gradedIdeal B P).colon {f} = gradedIdeal B P ∧
      gradedIdeal B P ⊔ Ideal.span {f} ≤ gradedIdeal B (sectionIdeal P (D ^ 2)) ∧
      (gradedIdeal B (sectionIdeal P (D ^ 2))).colon {g} = gradedIdeal B (sectionIdeal P D) ∧
      gradedIdeal B (sectionIdeal P (D ^ 2)) ⊔ Ideal.span {g} ≤ gradedIdeal B (sectionIdeal P D) := by
  classical
  obtain ⟨f, hf, hfmap⟩ := exists_slot_lift B i (D ^ 2) hD₂
  obtain ⟨g, hg, hgmap⟩ := exists_slot_lift B i D hD
  refine ⟨f, g, hf, hg, ?_, ?_, ?_, ?_⟩
  · apply gradedIdeal_colon hf
    intro a
    rw [hfmap]
    have h : IsLeftRegular (Ideal.Quotient.mk P (D ^ 2)) := by
      rw [map_pow]
      exact IsLeftRegular.pow 2 hr
    exact regular_colon h a
  · refine sup_le (gradedIdeal_mono B le_sup_left) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    rw [mem_gradedIdeal_of_grade hf, hfmap]
    exact (le_sup_right : Ideal.span {D ^ 2} ≤ sectionIdeal P (D ^ 2))
      (Ideal.mem_span_singleton_self _)
  · apply gradedIdeal_colon hg
    intro a
    rw [hgmap]
    exact square_colon hr a
  · refine sup_le (gradedIdeal_mono B (sup_le le_sup_left ?_))
      ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact ((Ideal.span_singleton_le_iff_mem _).mpr
        (Ideal.mem_span_singleton'.mpr ⟨D, (pow_two D).symm⟩)).trans le_sup_right
    · rw [mem_gradedIdeal_of_grade hg, hgmap]
      exact (le_sup_right : Ideal.span {D} ≤ sectionIdeal P D) (Ideal.mem_span_singleton_self _)
theorem diagonal_add (B : Family) (s t : Grade) :
    diagonalExponents B (s + t : Grade) = diagonalExponents B s + diagonalExponents B t := by
  ext m
  constructor
  · rintro ⟨u, hu, rfl⟩
    let v (i : Fin 5) (j : Fin (s i)) := u i (Fin.castAdd (t i) j)
    let w (i : Fin 5) (j : Fin (t i)) := u i (Fin.natAdd (s i) j)
    refine ⟨∑ i, ∑ j, v i j, ⟨v, fun i j => hu i _, rfl⟩,
      ∑ i, ∑ j, w i j, ⟨w, fun i j => hu i _, rfl⟩, ?_⟩
    simp only [v, w, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => (Fin.sum_univ_add (u i)).symm)
  · rintro ⟨a, ⟨v, hv, rfl⟩, b, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i => Fin.append (v i) (w i), ?_, ?_⟩
    · intro i
      exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hv i j)
        (fun j => by simpa only [Fin.append_right] using hw i j)
    · change (∑ i, ∑ j, v i j) + (∑ i, ∑ j, w i j) =
          ∑ i, ∑ j : Fin (s i + t i), Fin.append (v i) (w i) j
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa only [Fin.append_left, Fin.append_right] using
        (Fin.sum_univ_add (Fin.append (v i) (w i))).symm
private theorem diagonal_zero (B : Family) : diagonalExponents B (0 : Grade) = 0 := by
  ext m
  rw [Set.mem_zero]
  constructor
  · rintro ⟨u, _, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun _ j => j.elim0, fun _ j => j.elim0, by simp⟩
theorem diagonal_nsmul (B : Family) (t : Grade) (n : ℕ) :
    diagonalExponents B (n • t : Grade) = n • diagonalExponents B t := by
  induction n with
  | zero => simpa only [zero_smul] using diagonal_zero B
  | succ n ih => simp only [succ_nsmul, diagonal_add, ih]
private theorem zero_mem_diagonal (B : Family) (h0 : ∀ i, 0 ∈ B i) (t : Grade) : 0 ∈ diagonalExponents B t :=
  ⟨fun _ _ => 0, fun i _ => h0 i, by simp⟩
theorem generator_mem_diagonal {B : Family} (h0 : ∀ i, 0 ∈ B i) (v : Generator B) :
    v.2.val ∈ diagonalExponents B (slotWeight (slot B) v) := by
  classical
  let a (i : Fin 5) : Exponent := if i = v.1 then v.2.val else 0
  refine ⟨fun i _ => a i, ?_, ?_⟩
  · intro i _
    by_cases h : i = v.1
    · subst i
      simpa only [a, ite_eq_left rfl] using v.2.property
    · simpa only [a, ite_eq_right h] using h0 i
  · symm
    calc
      (∑ i, ∑ _j : Fin (slotWeight (slot B) v i), a i) =
          ∑ i, (slotWeight (slot B) v i) • a i :=
        Finset.sum_congr rfl fun i _ => Fin.sum_const _ _
      _ = v.2.val := by
        change (∑ i, (Finsupp.single v.1 (1 : ℕ) i) • a i) = _
        refine (Finset.sum_eq_single v.1 ?_ ?_).trans ?_
        · intro i _ h
          simp [a, h]
        · simp
        · simp [a]
private theorem tagged_monomial (B : Family) (d : Generator B →₀ ℕ) (c : GeoField) :
    taggedMap B (monomial d c) =
      monomial (Finsupp.weight (fun v : Generator B => v.2.val) d) c := by
  rw [taggedMap, aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, algebraMap_eq, C_mul_monomial, mul_one]
private theorem tagged_exponent_mem (B : Family) (h0 : ∀ i, 0 ∈ B i) (d : Generator B →₀ ℕ) :
    Finsupp.weight (fun v : Generator B => v.2.val) d ∈
      diagonalExponents B (Finsupp.weight (slotWeight (slot B)) d) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using zero_mem_diagonal B h0 (0 : Grade)
  | add a b ha hb => simpa only [map_add, diagonal_add] using Set.add_mem_add ha hb
  | single v n =>
      have hmem : n • v.2.val ∈ n • diagonalExponents B (slotWeight (slot B) v) := by
        induction n with
        | zero => simp
        | succ n ih =>
            simpa only [succ_nsmul] using Set.add_mem_add ih (generator_mem_diagonal h0 v)
      simpa only [Finsupp.weight_single, diagonal_nsmul] using hmem
private theorem tagged_lift {B : Family} {g : Grade} {m : Exponent}
    (hm : m ∈ diagonalExponents B g) :
    ∃ a : SlotRing B, a ∈ piece (slot B) g ∧ taggedMap B a = monomial m 1 := by
  classical
  obtain ⟨u, hu, rfl⟩ := hm
  let v (i : Fin 5) (j : Fin (g i)) : Generator B := ⟨i, ⟨u i j, hu i j⟩⟩
  let d : Generator B →₀ ℕ := ∑ i, ∑ j, Finsupp.single (v i j) 1
  have hg : Finsupp.weight (slotWeight (slot B)) d = g := by
    simp only [d, map_sum, Finsupp.weight_single, one_smul, slotWeight, slot, v, Fin.sum_const]
    ext i
    rw [Finsupp.finsetSum_apply]
    simp [unitGrade, Finsupp.single_apply]
  refine ⟨monomial d 1, isWeightedHomogeneous_monomial _ _ _ hg, ?_⟩
  simp only [tagged_monomial, d, map_sum, Finsupp.weight_single, one_smul, v]
private theorem tagged_image (B : Family) (h0 : ∀ i, 0 ∈ B i) (g : Grade) :
    (piece (slot B) g).map (taggedMap B).toLinearMap =
      restrictSupport GeoField (diagonalExponents B g) := by
  apply le_antisymm
  · have hpiece : piece (slot B) g =
        restrictSupport GeoField {d | Finsupp.weight (slotWeight (slot B)) d = g} :=
      weightedHomogeneousSubmodule_eq_finsupp_supported _ _ _
    rw [Submodule.map_le_iff_le_comap, hpiece, restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨d, hd, rfl⟩
    change taggedMap B (monomial d 1) ∈ restrictSupport GeoField (diagonalExponents B g)
    rw [tagged_monomial, monomial_mem_restrictSupport]
    exact Or.inl ((show Finsupp.weight (slotWeight (slot B)) d = g from hd) ▸
      tagged_exponent_mem B h0 d)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, heq⟩ := tagged_lift hm
    exact ⟨a, ha, heq⟩
open K1_13_6_2_4_1_2 (affine_image quotient_image_finrank)

theorem diagonal_hilbert (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (P : Ideal GeoJets5) (t : Grade) (n : ℕ) :
    gradedHilbert (slot B) (gradedIdeal B P) (n • t) =
      affineHilbertFunction (diagonalIdeal B P t) n := by
  let S := diagonalExponents B t
  change Module.finrank GeoField
      ((piece (slot B) (n • t)).map (Ideal.Quotient.mkₐ GeoField (gradedIdeal B P)).toLinearMap) =
    Module.finrank GeoField
      ((restrictTotalDegree S GeoField n).map
        (Ideal.Quotient.mkₐ GeoField (diagonalIdeal B P t)).toLinearMap)
  have hle : gradedIdeal B P ≤ P.comap (taggedMap B) :=
    Ideal.toIdeal_homogeneousCore_le (piece (slot B)) _
  have hgraded := quotient_image_finrank (piece (slot B) (n • t)) (gradedIdeal B P) P
    (taggedMap B) hle (fun _ ha => (mem_gradedIdeal_of_grade ha).mpr)
  have haffine := quotient_image_finrank (restrictTotalDegree S GeoField n) (diagonalIdeal B P t) P
    (monomialMap GeoField S) le_rfl (fun _ _ h => h)
  rw [hgraded, haffine, tagged_image B h0 (n • t), affine_image S (zero_mem_diagonal B h0 t) n,
    diagonal_nsmul]
theorem line_of_diagonal_agreement (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (t : Grade) (ht : ∀ j, 0 < t j)
    (hdiag : ∀ N, gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
      affineHilbertFunction (diagonalIdeal B P t) N) :
    line t p = affineHilbertPolynomial (diagonalIdeal B P t) := by
  obtain ⟨N₀, hN₀⟩ := hp
  refine eq_affineHilbertPolynomial_of_eval_eq (N₀ := N₀) fun N hN => ?_
  rw [line_eval, hN₀ _ (fun j => hN.trans (Nat.le_mul_of_pos_right N (ht j)))]
  exact congrArg (fun n : ℕ => (n : ℚ)) (hdiag N)
theorem diagonal_degree_le (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (t : Grade) {d : ℕ}
    (hd : DimLE P d) : (affineHilbertPolynomial (diagonalIdeal B P t)).natDegree ≤ d := by
  let f := monomialMap GeoField (diagonalExponents B t)
  let φ := Ideal.quotientMapₐ P f le_rfl
  exact (natDegree_affineHilbertPolynomial_le_of_injective φ Ideal.quotientMap_injective).trans
    (K1_13_6_2_4_2.hilbert_degree_le hd)
theorem gradedIdeal_degree_le (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) {d : ℕ} (hd : DimLE P d)
    {p : Form} (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    p.totalDegree ≤ d := by
  apply totalDegree_le_of_lines
  intro t ht
  rw [line_of_diagonal_agreement B P hp t ht (hdiag t ht)]
  exact diagonal_degree_le B P t hd
theorem mixedDegree_eq (B : Family) [∀ i, Finite (B i)] (P : Ideal GeoJets5) (I : Finset (Fin 5)) {p : Form}
    (hp : Represents p (fun t => gradedHilbert (slot B) (gradedIdeal B P) t))
    (hdiag : ∀ t : Grade, (∀ j, 0 < t j) → ∀ N,
      gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
        affineHilbertFunction (diagonalIdeal B P t) N) :
    mixedDegree B P I = p.coeff (squarefree I) / (2 : ℚ) ^ I.card := by
  unfold mixedDegree
  rw [← cube_extract I p]
  congr 1
  refine Finset.sum_congr rfl fun J _ => ?_
  have ht (j : Fin 5) : 0 < positiveDiagonal J j := by
    rw [positiveDiagonal_apply]
    split <;> decide
  have he := line_of_diagonal_agreement B P hp (positiveDiagonal J) ht
    (hdiag (positiveDiagonal J) ht)
  rw [he]
  rfl
private theorem top_coeff_mono {p q : Form} {a : Grade}
    (hp : p.totalDegree ≤ a.degree) (hq : q.totalDegree ≤ a.degree)
    (h : TopNonnegative (p - q)) : q.coeff a ≤ p.coeff a := by
  have hd : (p - q).totalDegree ≤ a.degree :=
    (totalDegree_sub p q).trans (max_le hp hq)
  exact sub_nonneg.mp (by simpa only [coeff_sub] using h a hd)
theorem properCut (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5)
    (hi : i ∉ I) (hdim : DimLE P (I.card + 1)) (D : GeoJets5)
    (hD : ∀ m ∈ D.support, m ∈ B i) (hD₂ : ∀ m ∈ (D ^ 2).support, m ∈ B i)
    (hreg : IsLeftRegular (Ideal.Quotient.mk P D)) :
    mixedDegree B (sectionIdeal P D) I ≤ mixedDegree B P (insert i I) := by
  let hcounts := K1_13_6_2_4_1_1.proof
  have hdiag (Q : Ideal GeoJets5) (t : Grade) (_ : ∀ j, 0 < t j) (n : ℕ) :=
    diagonal_hilbert B h0 Q t n
  let P₁ := sectionIdeal P D
  let P₂ := sectionIdeal P (D ^ 2)
  obtain ⟨f, g, hf, hg, hcf, hle₁, hcg, hle₂⟩ := exists_regular_lifts B P i D hD hD₂ hreg
  obtain ⟨hhom₁, hex₁⟩ := homogeneous_cut_exact (slot B) (gradedIdeal B P)
    (gradedIdeal_homogeneous B P) i f hf
  obtain ⟨hhom₂, hex₂⟩ := homogeneous_cut_exact (slot B) (gradedIdeal B P₂)
    (gradedIdeal_homogeneous B P₂) i g hg
  rw [hcf] at hex₁
  rw [hcg] at hex₂
  obtain ⟨p, _, hp, _, _⟩ := forms_of_counts hcounts (Generator B) (slot B) (gradedIdeal B P) (gradedIdeal B P)
    (gradedIdeal_homogeneous B P) (gradedIdeal_homogeneous B P) le_rfl
  obtain ⟨q, p₂, hq, hp₂, hpos₂⟩ := forms_of_counts hcounts (Generator B) (slot B)
    (gradedIdeal B P ⊔ Ideal.span {f}) (gradedIdeal B P₂) hhom₁
    (gradedIdeal_homogeneous B P₂) hle₁
  obtain ⟨r, p₁, hr, hp₁, hpos₁⟩ := forms_of_counts hcounts (Generator B) (slot B)
    (gradedIdeal B P₂ ⊔ Ideal.span {g}) (gradedIdeal B P₁) hhom₂
    (gradedIdeal_homogeneous B P₁) hle₂
  have hqeq : q = backwardDiff i p := eq_sub_previous i hq hp hp hex₁
  have hreq : r = p₂ - previous i p₁ := eq_sub_previous i hr hp₂ hp₁ hex₂
  have hreg₂ : IsLeftRegular (Ideal.Quotient.mk P (D ^ 2)) := by
    rw [map_pow]
    exact IsLeftRegular.pow 2 hreg
  have hdp := gradedIdeal_degree_le B P hdim hp (hdiag P)
  have hdp₁ := gradedIdeal_degree_le B P₁ (dim_le_after_section hreg hdim) hp₁ (hdiag P₁)
  have hdp₂ := gradedIdeal_degree_le B P₂ (dim_le_after_section hreg₂ hdim) hp₂ (hdiag P₂)
  have hdq : q.totalDegree ≤ I.card := by
    rw [hqeq]
    exact backwardDiff_degree_le i hdp
  have hdr : r.totalDegree ≤ I.card := by
    rw [hreq]
    exact (totalDegree_sub _ _).trans (max_le hdp₂ (previous_degree_le i hdp₁))
  have hdeg := squarefree_degree I
  have hm₂ := top_coeff_mono (hdq.trans_eq hdeg.symm) (hdp₂.trans_eq hdeg.symm) hpos₂
  have hm₁ := top_coeff_mono (hdr.trans_eq hdeg.symm) (hdp₁.trans_eq hdeg.symm) hpos₁
  rw [hqeq, backwardDiff_coeff_squarefree i hi hdp] at hm₂
  rw [hreq, coeff_sub, previous_coeff i (squarefree I) (hdp₁.trans_eq hdeg.symm)] at hm₁
  have hscaled : 2 * p₁.coeff (squarefree I) ≤ p.coeff (squarefree (insert i I)) := by
    linarith only [hm₁, hm₂]
  rw [mixedDegree_eq B P₁ I hp₁ (hdiag P₁), mixedDegree_eq B P (insert i I) hp (hdiag P)]
  rw [Finset.card_insert_of_notMem hi, pow_succ]
  refine (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) I.card)
    (mul_pos (pow_pos (by norm_num : (0 : ℚ) < 2) I.card) (by norm_num))).mpr ?_
  convert mul_le_mul_of_nonneg_right hscaled
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) I.card) using 1; ring
theorem diagonal_surjective {B : Family} (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i) {t : Grade}
    (ht : ∀ i, 0 < t i) : Function.Surjective (monomialMap GeoField (diagonalExponents B t)) := by
  classical
  apply monomialMap_surjective
  intro v
  obtain ⟨i, hi⟩ := hcoords v
  let j₀ : Fin (t i) := ⟨0, ht i⟩
  let u (k : Fin 5) (j : Fin (t k)) : Exponent :=
    if h : k = i then if h ▸ j = j₀ then Finsupp.single v 1 else 0 else 0
  refine ⟨u, ?_, ?_⟩
  · intro k j
    by_cases hk : k = i
    · subst k
      by_cases hj : j = j₀
      · simpa [u, hj] using hi
      · simpa [u, hj] using h0 i
    · simpa [u, hk] using h0 k
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j₀]
      · simp [u]
      · intro j _ hj
        simp [u, hj]
      · simp
    · intro k _ hk
      simp [u, hk]
    · simp


theorem mixedDegree_nonneg (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (P : Ideal GeoJets5) (I : Finset (Fin 5)) (hdim : DimLE P I.card) :
    0 ≤ mixedDegree B P I := by
  have htop : (⊤ : Ideal (SlotRing B)).IsHomogeneous (piece (slot B)) := by
    intro _ _ _
    trivial
  obtain ⟨p, q, hp, hq, hpos⟩ := forms_of_counts K1_13_6_2_4_1_1.proof
    (Generator B) (slot B) (gradedIdeal B P) ⊤ (gradedIdeal_homogeneous B P) htop le_top
  have hq0 : q = 0 := by
    obtain ⟨N, hN⟩ := hq
    apply K1_13_6_2_4_1.eq_of_grid (N := N)
    intro t ht
    rw [hN t ht]
    have hmap : (piece (slot B) t).map
        (Ideal.Quotient.mkₐ GeoField (⊤ : Ideal (SlotRing B))).toLinearMap = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨a, _, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (by trivial)
    simp [gradedHilbert, hmap]
  have hdiag (t : Grade) (_ : ∀ j, 0 < t j) (n : ℕ) := diagonal_hilbert B h0 P t n
  have hd := gradedIdeal_degree_le B P hdim hp hdiag
  rw [hq0, sub_zero] at hpos
  rw [mixedDegree_eq B P I hp hdiag]
  exact div_nonneg (hpos _ (hd.trans_eq (squarefree_degree I).symm)) (by positivity)

open K1_13_6_2_4_2 (dim_mono local_step weight weight_eq length_top)

private theorem mixed_step {B : Family} [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i) {I : Finset (Fin 5)}
    {J Q : Ideal GeoJets5} (hJ : DimLE J I.card) {a : GeoJets5}
    (ha : ∀ x, x * a ∈ J ↔ x ∈ Q) :
    mixedDegree B J I = mixedDegree B (sectionIdeal J a) I + mixedDegree B Q I := by
  classical
  have hdiag (U : Finset (Fin 5)) :
      let f := monomialMap GeoField (diagonalExponents B (positiveDiagonal U))
      (affineHilbertPolynomial (J.comap f)).coeff I.card =
        (affineHilbertPolynomial ((sectionIdeal J a).comap f)).coeff I.card +
          (affineHilbertPolynomial (Q.comap f)).coeff I.card := by
    let t := positiveDiagonal U
    have ht : ∀ i, 0 < t i := fun i => by rw [positiveDiagonal_apply]; split <;> decide
    let f := monomialMap GeoField (diagonalExponents B t)
    have hf : Function.Surjective f := diagonal_surjective h0 hcoords ht
    obtain ⟨A, hA⟩ := hf a
    change (affineHilbertPolynomial (J.comap f)).coeff I.card =
      (affineHilbertPolynomial ((sectionIdeal J a).comap f)).coeff I.card +
        (affineHilbertPolynomial (Q.comap f)).coeff I.card
    have hsection : (sectionIdeal J a).comap f = J.comap f ⊔ Ideal.span {A} := by
      have hk : J.comap f ⊔ Ideal.span {A} =
          (J.comap f ⊔ Ideal.span {A}) ⊔ Ideal.comap f ⊥ :=
        (sup_eq_left.mpr ((Ideal.comap_mono bot_le).trans le_sup_left)).symm
      calc
        (sectionIdeal J a).comap f = ((J.comap f ⊔ Ideal.span {A}).map f).comap f := by
          rw [Ideal.map_sup, Ideal.map_comap_of_surjective f hf, Ideal.map_span,
            Set.image_singleton, hA, sectionIdeal]
        _ = J.comap f ⊔ Ideal.span {A} :=
          (Ideal.comap_map_of_surjective f hf _).trans hk.symm
    have hAann (x : MvPolynomial (diagonalExponents B t) GeoField) :
        x * A ∈ J.comap f ↔ x ∈ Q.comap f := by
      simp only [Ideal.mem_comap, map_mul, hA, ha]
    have hd := diagonal_degree_le B J t hJ
    have hlow := K1_13_7_6_1.hilbertCoeff_step
      (J := J.comap f) (K := J.comap f ⊔ Ideal.span {A})
      le_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self A)) hAann hd
    rw [hsection]
    exact le_antisymm (K1_13_6_2_4_2_1.proof _ _ A hAann _ hd) hlow
  unfold mixedDegree
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  rw [hdiag U, mul_add]
private theorem cycleBudget {B : Family} [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i)
    {H : Ideal GeoJets5} {I : Finset (Fin 5)} (hH : DimLE H I.card)
    {ι : Type} (S : Finset ι) {C : ι → Ideal GeoJets5}
    (hinj : Set.InjOn C (S : Set ι)) (hp : ∀ a ∈ S, H.IsMinimalPrime (C a))
    (J : Ideal GeoJets5) (hHJ : H ≤ J) :
    (∀ a (ha : a ∈ S), LengthAt J (C a) (hp a ha).isPrime ≠ ⊤) ∧
      (∑ a ∈ S, (weight J (C a) : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B J I := by
  classical
  let D (P : Ideal GeoJets5) := mixedDegree B P I
  change _ ∧ (∑ a ∈ S, (weight J (C a) : ℚ) * D (C a)) ≤ D J
  revert hHJ
  induction J using WellFounded.induction (wellFounded_gt (α := Ideal GeoJets5)) with
  | h J ih =>
    intro hHJ
    by_cases hJ : J = ⊤
    · subst J
      have hz (a : ι) (ha : a ∈ S) : LengthAt ⊤ (C a) (hp a ha).isPrime = 0 :=
        length_top _ (hp a ha).isPrime
      constructor
      · intro a ha
        simp [hz a ha]
      · have hs : (∑ a ∈ S, (weight ⊤ (C a) : ℚ) * D (C a)) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          simp [weight_eq (hp a ha).isPrime, hz a ha]
        rw [hs]
        simp [D, mixedDegree, affineHilbertPolynomial_top]
    obtain ⟨a, Q, haJ, hQ, hann⟩ := K1_13_7_6_1.exists_prime_factor hJ
    let K := sectionIdeal J a
    have hJK : J ≤ K := le_sup_left
    have haK : a ∈ K := Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < K := lt_of_le_of_ne hJK fun he => haJ (he ▸ haK)
    have hHQ : H ≤ Q := fun x hx => (hann x).mp (J.mul_mem_right _ (hHJ hx))
    obtain ⟨hfinK, hboundK⟩ := ih K hlt (hHJ.trans hJK)
    have hstep (i : ι) (hi : i ∈ S) :
        LengthAt J (C i) (hp i hi).isPrime =
          (if Q = C i then 1 else 0) + LengthAt K (C i) (hp i hi).isPrime :=
      local_step hHJ hQ hann (hp i hi)
    have hDQ : 0 ≤ D Q := mixedDegree_nonneg B h0 Q I (dim_mono hHQ hH)
    have hweight (i : ι) (hi : i ∈ S) :
        (weight J (C i) : ℚ) = (weight K (C i) : ℚ) + (if Q = C i then 1 else 0) := by
      rw [weight_eq (hp i hi).isPrime, weight_eq (J := K) (hp i hi).isPrime, hstep i hi]
      split_ifs with hEq
      · rw [ENat.toNat_add (by simp) (hfinK i hi)]
        simp [add_comm]
      · simp
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hstep i hi]
      have hfinite : (if Q = C i then 1 else 0 : ℕ∞) ≠ ⊤ := by
        split_ifs <;> simp
      exact WithTop.add_ne_top.mpr ⟨hfinite, hfinK i hi⟩
    · have hindicator : (∑ i ∈ S, if Q = C i then D Q else 0) ≤ D Q := by
        by_cases hex : ∃ i ∈ S, Q = C i
        · obtain ⟨i, hi, he⟩ := hex
          rw [Finset.sum_eq_single_of_mem i hi, ite_eq_left he]
          intro j hj hji
          exact ite_eq_right fun hjQ => hji (hinj hj hi (hjQ.symm.trans he))
        · rw [Finset.sum_eq_zero (fun i hi => ite_eq_right (fun h => hex ⟨i, hi, h⟩))]
          exact hDQ
      calc
        _ = (∑ i ∈ S, (weight K (C i) : ℚ) * D (C i)) +
            (∑ i ∈ S, if Q = C i then D Q else 0) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hweight i hi, add_mul]
          split_ifs with he
          · rw [← he, one_mul]
          · rw [zero_mul]
        _ ≤ D K + D Q := add_le_add hboundK hindicator
        _ = D J := (mixed_step h0 hcoords (dim_mono hHJ hH) hann).symm
theorem cycleComparison (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i)
    (J : Ideal GeoJets5) (I : Finset (Fin 5)) (hJ : DimLE J I.card)
    {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ)
    (hinj : Set.InjOn C (S : Set ι))
    (h : ∀ a ∈ S, ∃ h : J.IsMinimalPrime (C a), (w a : ℕ∞) ≤ LengthAt J (C a) h.isPrime) :
    (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B J I := by
  have hp (a : ι) (ha : a ∈ S) : J.IsMinimalPrime (C a) := Exists.choose (h a ha)
  obtain ⟨hfin, hbudget⟩ := cycleBudget h0 hcoords hJ S hinj hp J le_rfl
  refine le_trans (Finset.sum_le_sum fun a ha => ?_) hbudget
  have hlen : (w a : ℕ∞) ≤ LengthAt J (C a) (hp a ha).isPrime := Exists.choose_spec (h a ha)
  have hw : w a ≤ weight J (C a) := by
    rw [weight_eq (hp a ha).isPrime]
    exact ENat.toNat_le_toNat hlen (hfin a ha)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hw)
    (mixedDegree_nonneg B h0 (C a) I (dim_mono (hp a ha).le hJ))

theorem divisorBound (B : Family) [∀ i, Finite (B i)] (h0 : ∀ i, 0 ∈ B i)
    (hcoords : ∀ v : Fin 5, ∃ i, Finsupp.single v 1 ∈ B i)
    (P : Ideal GeoJets5) (I : Finset (Fin 5)) (i : Fin 5)
    (hP : P.IsPrime) (hi : i ∉ I) (hd : OfDim P (I.card + 1))
    (D : GeoJets5) (hD : ∀ m ∈ D.support, m ∈ B i)
    (hD₂ : ∀ m ∈ (D ^ 2).support, m ∈ B i) (hprop : D ∉ P)
    {ι : Type} (S : Finset ι) (C : ι → Ideal GeoJets5) (w : ι → ℕ)
    (hinj : Set.InjOn C (S : Set ι)) (hcomp : ∀ a ∈ S, Component P D (C a) (w a)) :
    (∑ a ∈ S, (w a : ℚ) * mixedDegree B (C a) I) ≤ mixedDegree B P (insert i I) := by
  let := hP
  have hr : IsLeftRegular (Ideal.Quotient.mk P D) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hprop)
  have hdle : DimLE P (I.card + 1) := le_of_eq hd
  exact (cycleComparison B h0 hcoords (sectionIdeal P D) I (dim_le_after_section hr hdle)
    S C w hinj (fun a ha => ⟨(hcomp a ha).minimal, (hcomp a ha).length_le⟩)).trans
    (properCut B h0 P I i hi hdle D hD hD₂ hr)

end

end Low48BentCycle
