import ProximityPrize.SubmissionLower.Fast072
import ProximityPrize.SubmissionLower.Fast074
import ProximityPrize.SubmissionLower.Fast076
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
namespace K1_13_6_2_4_1
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (σ : Type) [Finite σ] (s : σ → Fin 5) (A C : Finset (σ →₀ ℕ)),
    outside C ⊆ outside A → ∃ p q : Form,
      Represents p (fun t => sliceCount s A t) ∧
      Represents q (fun t => sliceCount s C t) ∧ TopNonnegative (p - q)
def c2 : Prop :=
  ∀ (B : Boxes) (P : Ideal GeoJets5) (t : Grade), (∀ j, 0 < t j) → ∀ N : ℕ,
    gradedHilbert (slot B) (gradedIdeal B P) (N • t) =
      affineHilbertFunction (diagonalIdeal B P t) N
private theorem top_coeff_mono {p q : Form} {a : Grade}
    (hp : p.totalDegree ≤ a.degree) (hq : q.totalDegree ≤ a.degree)
    (h : TopNonnegative (p - q)) : q.coeff a ≤ p.coeff a := by
  have hd : (p - q).totalDegree ≤ a.degree :=
    (totalDegree_sub p q).trans (max_le hp hq)
  exact sub_nonneg.mp (by simpa only [coeff_sub] using h a hd)
theorem of_children (hcounts : c1) (hdiag : c2) :
    K1_13_6_2_4.c1 := by
  intro B _ P I i hi hdim D hbox hreg
  change mixedDegree B (sectionIdeal P D) I ≤ mixedDegree B P (insert i I)
  let P₁ := sectionIdeal P D
  let P₂ := sectionIdeal P (D ^ 2)
  obtain ⟨f, g, hf, hg, hcf, hle₁, hcg, hle₂⟩ := exists_regular_lifts B P i D hbox hreg
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
  have hdp := gradedIdeal_degree_le B P hdim hp (hdiag B P)
  have hdp₁ := gradedIdeal_degree_le B P₁ (dim_le_after_section hreg hdim) hp₁ (hdiag B P₁)
  have hdp₂ := gradedIdeal_degree_le B P₂ (dim_le_after_section hreg₂ hdim) hp₂ (hdiag B P₂)
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
  rw [mixedDegree_eq B P₁ I hp₁ (hdiag B P₁), mixedDegree_eq B P (insert i I) hp (hdiag B P)]
  rw [Finset.card_insert_of_notMem hi, pow_succ]
  refine (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) I.card)
    (mul_pos (pow_pos (by norm_num : (0 : ℚ) < 2) I.card) (by norm_num))).mpr ?_
  convert mul_le_mul_of_nonneg_right hscaled
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) I.card) using 1 <;> ring
end
end K1_13_6_2_4_1
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1_2
noncomputable section
open K1_13_6 K1_13_6_2 K1_13_6_2_4 K1_13_6_2_4_1 MvPolynomial
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
private theorem diagonal_add (B : Boxes) (s t : Grade) :
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
private theorem diagonal_zero (B : Boxes) : diagonalExponents B (0 : Grade) = 0 := by
  ext m
  rw [Set.mem_zero]
  constructor
  · rintro ⟨u, _, rfl⟩
    simp
  · rintro rfl
    exact ⟨fun _ j => j.elim0, fun _ j => j.elim0, by simp⟩
private theorem diagonal_nsmul (B : Boxes) (t : Grade) (n : ℕ) :
    diagonalExponents B (n • t : Grade) = n • diagonalExponents B t := by
  induction n with
  | zero => simpa only [zero_smul] using diagonal_zero B
  | succ n ih => simp only [succ_nsmul, diagonal_add, ih]
private theorem zero_mem_lattice (B : Boxes) (i : Fin 5) : 0 ∈ latticePoints (B i) :=
  allowed_zero _
private theorem zero_mem_diagonal (B : Boxes) (t : Grade) : 0 ∈ diagonalExponents B t :=
  ⟨fun _ _ => 0, fun i _ => zero_mem_lattice B i, by simp⟩
private theorem generator_mem_diagonal {B : Boxes} (v : Generator B) :
    v.2.val ∈ diagonalExponents B (slotWeight (slot B) v) := by
  classical
  let a (i : Fin 5) : Exponent := if i = v.1 then v.2.val else 0
  refine ⟨fun i _ => a i, ?_, ?_⟩
  · intro i _
    by_cases h : i = v.1
    · subst i
      simpa only [a, ite_eq_left rfl] using v.2.property
    · simpa only [a, ite_eq_right h] using zero_mem_lattice B i
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
private theorem tagged_monomial (B : Boxes) (d : Generator B →₀ ℕ) (c : GeoField) :
    taggedMap B (monomial d c) =
      monomial (Finsupp.weight (fun v : Generator B => v.2.val) d) c := by
  rw [taggedMap, aeval_monomial, Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
  simp only [monomial_pow, one_pow, ← monomial_sum_one, algebraMap_eq, C_mul_monomial, mul_one]
private theorem tagged_exponent_mem (B : Boxes) (d : Generator B →₀ ℕ) :
    Finsupp.weight (fun v : Generator B => v.2.val) d ∈
      diagonalExponents B (Finsupp.weight (slotWeight (slot B)) d) := by
  induction d using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using zero_mem_diagonal B (0 : Grade)
  | add a b ha hb => simpa only [map_add, diagonal_add] using Set.add_mem_add ha hb
  | single v n =>
      have hmem : n • v.2.val ∈ n • diagonalExponents B (slotWeight (slot B) v) := by
        induction n with
        | zero => simp
        | succ n ih =>
            simpa only [succ_nsmul] using Set.add_mem_add ih (generator_mem_diagonal v)
      simpa only [Finsupp.weight_single, diagonal_nsmul] using hmem
private theorem tagged_lift {B : Boxes} {g : Grade} {m : Exponent}
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
private theorem tagged_image (B : Boxes) (g : Grade) :
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
      tagged_exponent_mem B d)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, heq⟩ := tagged_lift hm
    exact ⟨a, ha, heq⟩
private theorem monomial_preimage {S : Set Exponent} {n : ℕ} {m : Exponent} (hm : m ∈ n • S) :
    ∃ a : MvPolynomial S GeoField, a.totalDegree ≤ n ∧
      monomialMap GeoField S a = monomial m 1 := by
  induction n generalizing m with
  | zero =>
      rw [zero_smul, Set.mem_zero] at hm
      subst m
      exact ⟨1, by simp, by simp⟩
  | succ n ih =>
      rw [succ_nsmul] at hm
      obtain ⟨b, hb, c, hc, rfl⟩ := hm
      obtain ⟨a, ha, hφ⟩ := ih hb
      refine ⟨a * MvPolynomial.X ⟨c, hc⟩, (totalDegree_mul _ _).trans ?_, ?_⟩
      · simpa only [totalDegree_X] using Nat.add_le_add_right ha 1
      · rw [map_mul, hφ, monomialMap_X, monomial_mul_monomial, one_mul]
private theorem affine_image (S : Set Exponent) (h0 : 0 ∈ S) (n : ℕ) :
    (restrictTotalDegree S GeoField n).map (monomialMap GeoField S).toLinearMap =
      restrictSupport GeoField (n • S) := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    exact monomialMap_mem_restrictSupport_nsmul h0 ((mem_restrictTotalDegree S n a).mp ha)
  · rw [restrictSupport_eq_span, Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, ha, hφ⟩ := monomial_preimage hm
    exact ⟨a, (mem_restrictTotalDegree S n a).mpr ha, hφ⟩
private theorem quotient_image_finrank {A : Type*} [CommRing A] [Algebra GeoField A]
    (V : Submodule GeoField A) (I : Ideal A) (P : Ideal GeoJets5) (φ : A →ₐ[GeoField] GeoJets5)
    (hle : I ≤ P.comap φ) (hker : ∀ a ∈ V, φ a ∈ P → a ∈ I) :
    Module.finrank GeoField (V.map (Ideal.Quotient.mkₐ GeoField I).toLinearMap) =
      Module.finrank GeoField ((V.map φ.toLinearMap).map
        (Ideal.Quotient.mkₐ GeoField P).toLinearMap) := by
  let W := V.map (Ideal.Quotient.mkₐ GeoField I).toLinearMap
  let f := Ideal.quotientMapₐ P φ hle
  have hinj : Function.Injective (f.toLinearMap.domRestrict W) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨x, hx⟩ hx0
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    change Ideal.Quotient.mk P (φ a) = 0 at hx0
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker a ha (Ideal.Quotient.eq_zero_iff_mem.mp hx0))
  have hmap : W.map f.toLinearMap =
      (V.map φ.toLinearMap).map (Ideal.Quotient.mkₐ GeoField P).toLinearMap := by
    simp only [W, ← Submodule.map_comp, ← AlgHom.comp_toLinearMap, f,
      Ideal.quotient_map_comp_mkₐ]
  rw [← hmap, ← LinearMap.range_domRestrict W f.toLinearMap]
  exact (LinearEquiv.ofInjective _ hinj).finrank_eq
theorem proof : K1_13_6_2_4_1.c2 := by
  intro B P t _ n
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
  rw [hgraded, haffine, tagged_image B (n • t), affine_image S (zero_mem_diagonal B t) n,
    diagonal_nsmul]
end
end K1_13_6_2_4_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_2_4_1_1
open K1_13_6_2_4_1 MvPolynomial
open scoped BigOperators
theorem represents_cell_sum {σ : Type} [Fintype σ] (s : σ → Fin 5)
    (b : σ →₀ ℕ) (A : Finset (σ →₀ ℕ)) (hA : ∀ a ∈ A, a ≤ b) :
    Represents (∑ u ∈ cells (b := b) A, cellForm s u) (fun t => sliceCount s A t) := by
  refine ⟨b.degree + 1, fun t ht => ?_⟩
  change eval (fun j => (t j : ℚ)) (∑ u ∈ cells (b := b) A, cellForm s u) =
    (sliceCount s A t : ℚ)
  rw [map_sum, sliceCount_eq_sum s b A hA, Nat.cast_sum]
  exact Finset.sum_congr rfl fun u _ => cellForm_eval s u t (fun j => Nat.lt_of_succ_le (ht j))
theorem proof : K1_13_6_2_4_1.c1 := by
  classical
  intro σ _ s A C h
  let _ := Fintype.ofFinite σ
  let b := (A ∪ C).sup id
  let U := cells (b := b) A
  let V := cells (b := b) C
  refine ⟨∑ u ∈ U, cellForm s u, ∑ u ∈ V, cellForm s u, ?_, ?_, ?_⟩
  · exact represents_cell_sum s b A (fun _ ha => Finset.le_sup (f := id) (Finset.mem_union_left C ha))
  · exact represents_cell_sum s b C (fun _ hc => Finset.le_sup (f := id) (Finset.mem_union_right A hc))
  · rw [← Finset.sum_sdiff (cells_mono (b := b) h) (f := cellForm s), add_sub_cancel_right]
    exact top_sum _ _ (fun u _ => cellForm_top s u)
end K1_13_6_2_4_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1
noncomputable section
open K1_13_6 K1_13_7_1 K1_13_7_1_1_1 MvPolynomial
open K1_13_6_2_4_1 (Grade Form Represents TopNonnegative gradedHilbert piece slotWeight
  outside sliceCount standard_piece_rank)
open scoped Pointwise
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def c1 : Prop :=
  ∀ (A : Fin 4 → Set Exponent) (B : Set Exponent), admissible A B →
    ∀ (P : Ideal GeoJets) (t : Grade),
      gradedHilbert (tagSlot A B) (tagIdeal A B P) t =
        hilbertRank A B P (t 4) (fun i => t i.castSucc)
def c2 : Prop :=
  ∀ (σ : Type) [Finite σ] (s : σ → Fin 5) (T : Finset (σ →₀ ℕ)),
    ∃ p : Form, Represents p (fun t => sliceCount s T t) ∧ TopNonnegative p
theorem graded_footprint (σ : Type) [Finite σ] (s : σ → Fin 5)
    (J : Ideal (MvPolynomial σ GeoField)) (hJ : J.IsHomogeneous (piece s)) :
    ∃ T : Finset (σ →₀ ℕ), ∀ t : Grade, gradedHilbert s J t = sliceCount s T t := by
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨T, hT⟩ := m.exists_finset_standardExponents_iff J
  have hstandard : m.standardExponents J = outside T := Set.ext hT
  refine ⟨T, fun t => ?_⟩
  rw [standard_piece_rank s m J hJ t, hstandard]
  rfl
theorem form_of_rank (himage : c1) (hcounts : c2)
    {A : Fin 4 → Set Exponent} {B : Set Exponent} (hAB : admissible A B) (P : Ideal GeoJets) :
    ∃ p : Form, Represents p (fun t => (hilbertRank A B P (t 4) (fun i => t i.castSucc) : ℚ)) ∧
      TopNonnegative p := by
  let : ∀ j, Finite (slotSupport A B j) := fun j => by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · unfold slotSupport
      rw [Fin.lastCases_last]
      exact hAB.2.1.to_subtype
    · unfold slotSupport
      rw [Fin.lastCases_castSucc]
      exact (hAB.1 i).1.to_subtype
  let J := tagIdeal A B P
  let s := tagSlot A B
  have hJ : J.IsHomogeneous (piece s) :=
    ((P.comap (tagEval A B)).homogeneousCore (piece s)).isHomogeneous
  obtain ⟨T, hT⟩ := graded_footprint (TaggedVar A B) s J hJ
  obtain ⟨p, ⟨N, hN⟩, hp⟩ := hcounts (TaggedVar A B) s T
  refine ⟨p, ⟨N, fun t ht => ?_⟩, hp⟩
  exact (hN t ht).trans
    (congrArg (fun n : ℕ => (n : ℚ)) ((hT t).symm.trans (himage A B hAB P t)))
theorem zero_mem_copies {S : Set Exponent} (h : 0 ∈ S) (n : ℕ) : 0 ∈ n • S := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul]
    simpa only [zero_add] using Set.add_mem_add ih h
theorem finrank_of_contains_one {K R : Type} [Field K] [CommRing R] [Algebra K R]
    (e : R ≃ₐ[K] K) (S : Submodule K R) (h : 1 ∈ S) :
    Module.finrank K S = 1 := by
  have htop : S = ⊤ := by
    apply top_unique
    intro r _
    have hs : (e r) • (1 : R) = r := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv ((e r) • (1 : R)) = (e r) • (e 1) :=
          e.toLinearEquiv.map_smul (e r) 1
        _ = e.toLinearEquiv r := by
          change (e r) • (e 1) = e r
          have he : e (1 : R) = (1 : K) := map_one e
          rw [he, smul_eq_mul, mul_one]
    exact hs ▸ S.smul_mem (e r) h
  calc
    Module.finrank K S = Module.finrank K (⊤ : Submodule K R) :=
      congrArg (fun T : Submodule K R => Module.finrank K T) htop
    _ = Module.finrank K R := finrank_top K R
    _ = Module.finrank K K := e.toLinearEquiv.finrank_eq
    _ = 1 := Module.finrank_self K
theorem eval_piece_finrank {K : Type} [Field K] (y : Fin 4 → K)
    {T : Set Exponent} (hT : 0 ∈ T) :
    Module.finrank K ((restrictSupport K T).map
      (Ideal.Quotient.mkₐ K (RingHom.ker (eval y))).toLinearMap) = 1 := by
  let f : MvPolynomial (Fin 4) K →ₐ[K] K := aeval y
  have hf : Function.Surjective f := fun c => ⟨C c, by simp [f]⟩
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let q := Ideal.Quotient.mkₐ K (RingHom.ker f.toRingHom)
  have h1 : (1 : MvPolynomial (Fin 4) K) ∈ restrictSupport K T := by
    rw [MvPolynomial.one_def]
    exact (monomial_mem_restrictSupport K).mpr (Or.inl hT)
  have hm : 1 ∈ (restrictSupport K T).map q.toLinearMap :=
    Submodule.mem_map.mpr ⟨1, h1, q.map_one⟩
  exact finrank_of_contains_one e _ hm
theorem point_hilbert {A : Fin 4 → Set Exponent} {B : Set Exponent} (hAB : admissible A B)
    (y : GeoPoint) (b : ℕ) (w : Grades) : hilbert A B (pointIdeal y) b w = 1 := by
  have hzero {S T : Set Exponent} (hs : 0 ∈ S) (ht : 0 ∈ T) : 0 ∈ S + T := by
    simpa only [zero_add] using Set.add_mem_add hs ht
  have hz : 0 ∈ gradedExponents A B b w :=
    hzero (hzero (hzero (hzero (zero_mem_copies hAB.2.2.1 b)
      (zero_mem_copies (hAB.1 0).2 (w 0)))
      (zero_mem_copies (hAB.1 1).2 (w 1)))
      (zero_mem_copies (hAB.1 2).2 (w 2)))
      (zero_mem_copies (hAB.1 3).2 (w 3))
  unfold hilbert
  rw [eval_piece_finrank y hz, Nat.cast_one]
theorem of_children (himage : c1) (hcounts : c2) : K1_13_7_1_1_1.c1 := by
  classical
  intro A B hAB
  have hex (i : Fin 5) (P : Ideal GeoJets) (hd : affineDim P = 4 - i.val) :
      ∃ d : ℝ, 0 ≤ d ∧ IsMixedDegree A B P i.val d := by
    obtain ⟨p, hp, hpos⟩ := form_of_rank himage hcounts hAB P
    exact mixed_of_polynomial hp i ((polynomial_degree_bound hAB P hp).trans_eq hd) hpos
  let D (i : Fin 5) (P : Ideal GeoJets) : ℝ :=
    if i = 4 ∧ P ∈ Set.range pointIdeal then 1
    else if hd : affineDim P = 4 - i.val then Classical.choose (hex i P hd) else 0
  refine ⟨D, ?_, fun y => ite_eq_left ⟨rfl, ⟨y, rfl⟩⟩⟩
  intro i P _ hd
  by_cases h : i = 4 ∧ P ∈ Set.range pointIdeal
  · have hD : D i P = 1 := ite_eq_left h
    rw [hD]
    obtain ⟨rfl, y, rfl⟩ := h
    refine ⟨zero_le_one, 0, ?_⟩
    have hz : remainingDirections (4 : Fin 5).val = [] := by decide
    intro b w s _ _
    have he : 4 - (4 : Fin 5).val = 0 := by decide
    rw [hz, he]
    change hilbert A B (pointIdeal y) b w = (s : ℝ) ^ (0 : ℕ) * 1
    rw [point_hilbert hAB y b w, pow_zero, mul_one]
  · have hD : D i P = Classical.choose (hex i P hd) := by
      dsimp only [D]
      rw [ite_eq_right h, dite_eq_left hd]
    rw [hD]
    exact Classical.choose_spec (hex i P hd)
end
end K1_13_7_1_1_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1_1
noncomputable section
open K1_13_6 K1_13_6_2_4_1 K1_13_7_1_1_1 K1_13_7_1_1_1_1 K1_13_7_1_1_1_2
open MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
theorem slotSupport_eq (A : Fin 4 → Set Exponent) (B : Set Exponent) :
    slotSupport A B = supportIn A B := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [slotSupport, Fin.lastCases_last, supportIn_last]
  · rw [slotSupport, Fin.lastCases_castSucc, supportIn_castSucc]
theorem proof : K1_13_7_1_1_1_1.c1 := by
  intro A B hAB P t
  let rankFor (S : Fin 5 → Set Exponent) : ℕ :=
    let s : ((j : Fin 5) × S j) → Fin 5 := Sigma.fst
    let f : MvPolynomial ((j : Fin 5) × S j) GeoField →ₐ[GeoField] GeoJets :=
      aeval fun v => monomial v.2.val 1
    gradedHilbert s ((P.comap f).homogeneousCore (piece s)).toIdeal t
  have hRank : gradedHilbert (tagSlot A B) (tagIdeal A B P) t =
      gradedHilbert (slot A B) (liftIdeal A B P) t :=
    congrArg rankFor (slotSupport_eq A B)
  rw [hRank]
  have h := K1_13_7_1_1_1_2_2.proof A B hAB P (gridOf t)
  change (gradedHilbert (slot A B) (liftIdeal A B P) (multigrade (gridOf t)) : ℝ) =
    (hilbertRank A B P (t 4) (fun i => t i.castSucc) : ℝ) at h
  rw [multigrade_gridOf] at h
  exact_mod_cast h
end
end K1_13_7_1_1_1_1_1
end
section
set_option autoImplicit false
namespace K1_13_7_1_1_1_1_2
open K1_13_6_2_4_1 K1_13_6_2_4_1_1 MvPolynomial
open scoped BigOperators
theorem proof : K1_13_7_1_1_1_1.c2 := by
  classical
  intro σ _ s T
  let _ := Fintype.ofFinite σ
  let b := T.sup id
  have hb : ∀ a ∈ T, a ≤ b := fun _ ha => Finset.le_sup (f := id) ha
  refine ⟨∑ u ∈ cells (b := b) T, cellForm s u, ?_, ?_⟩
  · refine ⟨b.degree + 1, fun t ht => ?_⟩
    change eval (fun j => (t j : ℚ)) (∑ u ∈ cells (b := b) T, cellForm s u) =
      (sliceCount s T t : ℚ)
    rw [map_sum, sliceCount_eq_sum s b T hb, Nat.cast_sum]
    exact Finset.sum_congr rfl fun u _ => cellForm_eval s u t (fun j => Nat.lt_of_succ_le (ht j))
  · exact top_sum _ _ (fun u _ => cellForm_top s u)
end K1_13_7_1_1_1_1_2
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_2_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_2_3 K1_13_6_2_3_2 K1_13_7_1 MvPolynomial Filter
open K1_13_6_2_3_2_5 (ray_top totalDegree_le_of_ray_degree deltas_top shapeSum_add shapeSum_step)
def finiteMonomialOrder (σ : Type) [Finite σ] : MonomialOrder σ := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let _ : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact MonomialOrder.degLex
theorem form_of_cap {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → Shape)
    (hs : ∀ i, Chamber (s i)) (J : Ideal GeoJets) (used : List ι) :
    let H := fun a => (supportRank J (capExponents (shapeSum s a)) : ℚ)
    ∃ F : MvPolynomial ι ℚ, (∀ᶠ a in atTop, eval (fun i => (a i : ℚ)) F = H a) ∧
      ∀ᶠ a in atTop, 0 ≤ deltas used H a := by
  classical
  let σ := CapVar s
  let m := finiteMonomialOrder σ
  let I := capIdeal s J
  let slot := capSlot s
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff I
  have hzero : outside ({0} : Finset (σ →₀ ℕ)) = ∅ := by
    ext e
    simp [outside, zero_le]
  obtain ⟨⟨F, hF⟩, hpos⟩ := K1_13_6_2_3_2_1.proof slot A {0}
    (by rw [hzero]; exact Set.empty_subset _)
  have hcount (a : ι → ℕ) :
      sliceCount slot A a - sliceCount slot {0} a =
        (supportRank J (capExponents (shapeSum s a)) : ℚ) := by
    have hset : m.standardExponents I = outside A := Set.ext hA
    have hstd := standard_rank slot m I (K1_13_6_2_3_2_3.proof s J).1 a
    rw [hset] at hstd
    have he : sliceCount slot A a = hilbert slot I a := hstd.symm
    rw [he, (K1_13_6_2_3_2_3.proof s J).2 a, weak_packing s hs]
    simp [sliceCount, hzero]
  exact ⟨F, by simpa only [hcount] using hF, by simpa only [hcount] using hpos used⟩
private theorem deltas_congr_of_ge {ι : Type} [DecidableEq ι]
    (used : List ι) {F G : (ι → ℕ) → ℚ} {u : ι → ℕ}
    (h : ∀ a ≥ u, F a = G a) (a : ι → ℕ) (ha : u ≤ a) :
    deltas used F a = deltas used G a := by
  induction used generalizing a with
  | nil => exact h a ha
  | cons i rest ih =>
    simp only [deltas, ih a ha, ih (a + step i) (ha.trans fun j => Nat.le_add_right _ _)]
theorem proof : K1_13_7_2_3_1_2.c2 := by
  intro J _ hJ p q hp hq
  let s : Fin 3 → Shape := ![⟨3, 3, 1⟩, p, q]
  let used : List (Fin 3) := [1, 2]
  have hs (i : Fin 3) : Chamber (s i) := by
    fin_cases i
    · change Chamber ⟨3, 3, 1⟩
      exact ⟨by decide, by decide⟩
    · exact hp
    · exact hq
  have hbase : 0 < (s 0).t := by
    change 0 < (1 : ℕ)
    decide
  obtain ⟨F, hF, hpos⟩ := form_of_cap s hs J used
  obtain ⟨u, hu⟩ := eventually_atTop.mp hF
  have hray (v : Fin 3 → ℕ) (hv : 0 < v 0) :=
    weak_ray_compare s J 0 hs hbase F u hu v hv used.length hJ.le
  have hdeg : F.totalDegree ≤ used.length :=
    (totalDegree_le_of_ray_degree F u (dimension J) (fun v hv => (hray v (hv 0)).1)).trans hJ.le
  let G := fun v : Fin 3 → ℕ => eval (fun i => (v i : ℚ)) (homogeneousComponent used.length F)
  have hG (v : Fin 3 → ℕ) (hv : step 0 ≤ v) :
      G v = capCoeff J used.length (shapeSum s v) := by
    have hv₀ : 0 < v 0 :=
      Nat.zero_lt_one.trans_le (by simpa [step] using hv 0)
    exact (ray_top F u v hdeg).symm.trans (hray v hv₀).2
  obtain ⟨a, ha, hau⟩ := (hpos.and (eventually_ge_atTop u)).exists
  have hnon : 0 ≤ deltas used (fun v => capCoeff J used.length (shapeSum s v)) (step 0) := calc
    _ ≤ deltas used (fun v => (supportRank J (capExponents (shapeSum s v)) : ℚ)) a := ha
    _ = deltas used (fun v => eval (fun i => (v i : ℚ)) F) a :=
      (deltas_congr_of_ge used hu a hau).symm
    _ = deltas used G (step 0) := deltas_top used (by decide) F hdeg a (step 0)
    _ = _ := deltas_congr_of_ge used hG (step 0) le_rfl
  have hs₀ : s 0 = ⟨3, 3, 1⟩ := rfl
  have hs₁ : s 1 = p := rfl
  have hs₂ : s 2 = q := rfl
  have hpol : 0 ≤ polarize (capCoeff J 2) [p, q] ⟨3, 3, 1⟩ := by
    simpa only [used, deltas, shapeSum_add, shapeSum_step, hs₀, hs₁, hs₂, polarize,
      List.length_cons, List.length_nil, Nat.reduceAdd] using hnon
  unfold mixedDegree
  exact div_nonneg hpol (by positivity)
end
end K1_13_7_2_3_1_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
namespace K1_10_1_1
noncomputable section
open K1 K1_10 K1_10_1 K1_11 K1_11_2 MvPolynomial
abbrev lift5 {F : Type*} [Field F] :=
  Polynomial.toMvPolynomial (R := F) (0 : Fin 5)
def pencil5 {F : Type*} [Field F] (z : Fin 5) (A : Fin 2 → Polynomial F) :
    MvPolynomial (Fin 5) F :=
  lift5 (A 0) + lift5 (A 1) * MvPolynomial.X z
def output5 {F : Type*} [Field F] (O : Fin 2 → Fin 2 → Polynomial F) :
    MvPolynomial (Fin 5) F :=
  pencil5 3 (fun j => O j 0) + pencil5 3 (fun j => O j 1) * MvPolynomial.X 4
theorem lift5_view (P : Polynomial K) :
    polynomialView (lift5 P) = Polynomial.C (liftOrdinary P) := by
  have h : (polynomialView (F := K)).toRingHom.comp (lift5 (F := K)).toRingHom =
      Polynomial.C.comp liftOrdinary := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [lift5, liftOrdinary, polynomialView, finSuccEquiv_apply]
    · simp [lift5, liftOrdinary, polynomialView_X]
  exact RingHom.congr_fun h P
theorem planeRelation_eq (U V : Fin 2 → Polynomial K)
    (O : Fin 2 → Fin 2 → Polynomial K) :
    planeRelation U V O =
      pencil5 4 U * MvPolynomial.X 1 + pencil5 3 V * MvPolynomial.X 2 - output5 O := by
  have h1 : polynomialView (F := K) (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X 1) :=
    polynomialView_X 1
  have h2 : polynomialView (F := K) (MvPolynomial.X 2) = Polynomial.X :=
    polynomialView_X 2
  have h3 : polynomialView (F := K) (MvPolynomial.X 3) = Polynomial.C (MvPolynomial.X 2) :=
    polynomialView_X 3
  have h4 : polynomialView (F := K) (MvPolynomial.X 4) = Polynomial.C (MvPolynomial.X 3) :=
    polynomialView_X 4
  apply (polynomialView (F := K)).injective
  simp only [planeRelation_view, pencil5, output5, map_sub, map_add, map_mul,
    lift5_view, h1, h2, h3, h4, denominator, numerator, pencil]
  ring
variable {F : Type*} [Field F]
theorem lift5_support (P : Polynomial F) (e : Fin 5 →₀ ℕ) :
    e ∈ (lift5 P).support ↔ ∃ n ∈ P.support, e = Finsupp.single 0 n := by
  classical
  let f : Unit → Fin 5 := fun _ => 0
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  change e ∈ (Polynomial.toMvPolynomial (0 : Fin 5) P).support ↔ _
  rw [Polynomial.toMvPolynomial_eq_rename_comp]
  change e ∈ (rename f ((uniqueAlgEquiv F Unit).symm P)).support ↔ _
  rw [support_rename_of_injective hf, Finset.mem_image]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d default, ?_, ?_⟩
    · simpa only [MvPolynomial.mem_support_iff, coeff_uniqueAlgEquiv_symm, Polynomial.mem_support_iff] using hd
    · calc
        Finsupp.mapDomain f d = Finsupp.mapDomain f (Finsupp.single default (d default)) :=
          congrArg (Finsupp.mapDomain f) (Finsupp.unique_single d)
        _ = Finsupp.single 0 (d default) := by rw [Finsupp.mapDomain_single]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨Finsupp.single default n, ?_, ?_⟩
    · simpa only [MvPolynomial.mem_support_iff, coeff_uniqueAlgEquiv_symm, Finsupp.single_eq_same,
        Polynomial.mem_support_iff] using hn
    · rw [Finsupp.mapDomain_single]
theorem lift5_degree (P : Polynomial F) (i : Fin 5) :
    (lift5 P).degreeOf i = if i = 0 then P.natDegree else 0 := by
  rw [degreeOf_eq_sup]
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    obtain ⟨n, hn, rfl⟩ := (lift5_support P e).mp he
    by_cases hi : i = 0
    · subst i
      simpa using Polynomial.le_natDegree_of_mem_supp n hn
    · simp [hi]
  · by_cases hi : i = 0
    · subst i
      by_cases hz : P = 0
      · simp [hz]
      have he := (lift5_support P (Finsupp.single 0 P.natDegree)).mpr
        ⟨P.natDegree, Polynomial.natDegree_mem_support_of_nonzero hz, rfl⟩
      simpa using Finset.le_sup (f := fun e : Fin 5 →₀ ℕ => e 0) he
    · simp [hi]
theorem pencil5_disjoint (A : Fin 2 → Polynomial F) {z : Fin 5} (hz : z ≠ 0) :
    Disjoint (lift5 (A 0)).support (lift5 (A 1) * MvPolynomial.X z).support := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  obtain ⟨n, _, rfl⟩ := (lift5_support (A 0) e).mp he
  rw [support_mul_X] at he'
  obtain ⟨d, hd, heq⟩ := Finset.mem_map.mp he'
  obtain ⟨m, _, rfl⟩ := (lift5_support (A 1) d).mp hd
  have h := congrArg (fun a : Fin 5 →₀ ℕ => a z) heq
  simp [Finsupp.add_apply, Ne.symm hz] at h
theorem pencil5_ne (A : Fin 2 → Polynomial F) {z : Fin 5} (hz : z ≠ 0)
    (hA : ∃ j, A j ≠ 0) : pencil5 z A ≠ 0 := by
  have hn (j : Fin 2) (hj : A j ≠ 0) : lift5 (A j) ≠ 0 := by
    intro h
    exact hj ((Polynomial.toMvPolynomial_injective (0 : Fin 5)) (h.trans (map_zero lift5).symm))
  have hs : (pencil5 z A).support =
      (lift5 (A 0)).support ∪ (lift5 (A 1) * MvPolynomial.X z).support :=
    Finsupp.support_add_eq (pencil5_disjoint A hz)
  apply support_nonempty.mp
  rw [hs]
  obtain ⟨j, hj⟩ := hA
  fin_cases j
  · exact (support_nonempty.mpr (hn 0 hj)).mono Finset.subset_union_left
  · exact (support_nonempty.mpr (mul_ne_zero (hn 1 hj) (X_ne_zero z))).mono Finset.subset_union_right
theorem pencil5_degree_x (A : Fin 2 → Polynomial F) {z : Fin 5} (hz : z ≠ 0) :
    (pencil5 z A).degreeOf 0 = max (A 0).natDegree (A 1).natDegree := by
  rw [pencil5, ← weightedTotalDegree_piSingle, weighted_add_of_disjoint _ _ _ (pencil5_disjoint A hz),
    weightedTotalDegree_piSingle, weightedTotalDegree_piSingle,
    degreeOf_mul_X_of_ne _ (Ne.symm hz)]
  simp [lift5_degree]
theorem pencil5_degree_le (A : Fin 2 → Polynomial F) (i z : Fin 5) (d : ℕ)
    (hA : ∀ j, (A j).natDegree ≤ d) :
    (pencil5 z A).degreeOf i ≤ (if i = 0 then d else 0) + (if i = z then 1 else 0) := by
  have h (j : Fin 2) : (lift5 (A j)).degreeOf i ≤ if i = 0 then d else 0 := by
    rw [lift5_degree]
    split <;> simp [hA]
  refine (degreeOf_add_le i _ _).trans (max_le ?_ ?_)
  · exact (h 0).trans (Nat.le_add_right _ _)
  · exact (degreeOf_mul_le i _ _).trans (by rw [degreeOf_X]; exact Nat.add_le_add_right (h 1) _)
theorem output5_degree_le (O : Fin 2 → Fin 2 → Polynomial F) (i : Fin 5) (d : ℕ)
    (hO : ∀ j l, (O j l).natDegree ≤ d) :
    (output5 O).degreeOf i ≤
      (if i = 0 then d else 0) + (if i = 3 then 1 else 0) + (if i = 4 then 1 else 0) := by
  have h (l : Fin 2) := pencil5_degree_le (fun j => O j l) i 3 d (fun j => hO j l)
  refine (degreeOf_add_le i _ _).trans (max_le ?_ ?_)
  · exact (h 0).trans (Nat.le_add_right _ _)
  · exact (degreeOf_mul_le i _ _).trans (by rw [degreeOf_X]; exact Nat.add_le_add_right (h 1) _)
theorem proof : K1_10_1.c1 := by
  intro u deleted h U V W j
  let A := pencil5 4 U
  let B := pencil5 3 V
  let O := output5 W.output
  have hA : ∀ l, (U l).natDegree ≤ h := by
    intro l
    have hh := W.height_eq
    unfold amplitudeDegree at hh
    fin_cases l
    · change (U 0).natDegree ≤ h
      omega
    · change (U 1).natDegree ≤ h
      omega
  have hB : ∀ l, (V l).natDegree ≤ h := by
    intro l
    have hh := W.height_eq
    unfold amplitudeDegree at hh
    fin_cases l
    · change (V 0).natDegree ≤ h
      omega
    · change (V 1).natDegree ≤ h
      omega
  have hO : ∀ k l, (W.output k l).natDegree ≤ 131071 + h := by
    intro k l
    by_cases hz : W.output k l = 0
    · simp [hz]
    · have hh := W.output_degree k l
      rw [Polynomial.degree_eq_natDegree hz, Nat.cast_lt] at hh
      omega
  have hAd (i : Fin 5) := pencil5_degree_le U i 4 h hA
  have hBd (i : Fin 5) := pencil5_degree_le V i 3 h hB
  have hOd (i : Fin 5) := output5_degree_le W.output i (131071 + h) hO
  have hAm : OmitsMessages A := ⟨by simpa [A] using hAd 1, by simpa [A] using hAd 2⟩
  have hBm : OmitsMessages B := ⟨by simpa [B] using hBd 1, by simpa [B] using hBd 2⟩
  have hOm : OmitsMessages O := ⟨by simpa [O] using hOd 1, by simpa [O] using hOd 2⟩
  have hheight : max (A.degreeOf 0) (B.degreeOf 0) = h := by
    simpa [A, B, pencil5_degree_x _ (by decide : (4 : Fin 5) ≠ 0),
      pencil5_degree_x _ (by decide : (3 : Fin 5) ≠ 0), amplitudeDegree] using W.height_eq
  rw [planeRelation_eq]
  change (A * MvPolynomial.X 1 + B * MvPolynomial.X 2 - O).weightedTotalDegree _ = _
  rw [linear_form_weight _ _ _ _ (pencil5_ne U (by decide) W.U_ne)
    (pencil5_ne V (by decide) W.V_ne) hAm hBm hOm,
    omitted_source_weights _ _ hAm, omitted_source_weights _ _ hBm,
    omitted_source_weights _ _ hOm]
  fin_cases j
  · have hOx : O.degreeOf 0 ≤ 131071 + h := by simpa [O] using hOd 0
    simp [sourceWeights, relationBounds]
    omega
  · simp [sourceWeights, relationBounds]
  · have hAs : A.degreeOf 3 = 0 := by simpa [A] using hAd 3
    have hBs : B.degreeOf 3 ≤ 1 := by simpa [B] using hBd 3
    have hOs : O.degreeOf 3 ≤ 1 := by simpa [O] using hOd 3
    simp [sourceWeights, relationBounds, hAs]
    omega
  · have hAt : A.degreeOf 4 ≤ 1 := by simpa [A] using hAd 4
    have hBt : B.degreeOf 4 = 0 := by simpa [B] using hBd 4
    have hOt : O.degreeOf 4 ≤ 1 := by simpa [O] using hOd 4
    simp [sourceWeights, relationBounds, hBt]
    omega
end
end K1_10_1_1
end
section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace K1_11_2_2
noncomputable section
open MvPolynomial K1_11_2
variable {F : Type*} [Field F]
private def pencil (j : Fin 5) (a b : F) : MvPolynomial (Fin 5) F := C a + MvPolynomial.X j * C b
def nodeValue (x a b c d : F) (U V : MvPolynomial (Fin 5) F) : MvPolynomial (Fin 5) F :=
  parameterNode x U * pencil 3 a b + parameterNode x V * pencil 4 c d
theorem nodeWord_combination (x a b c d : F) (U V : MvPolynomial (Fin 5) F)
    (hU : OmitsMessages U) (hV : OmitsMessages V) :
    nodeWordMap x a b c d (U * MvPolynomial.X 1 + V * MvPolynomial.X 2) = nodeValue x a b c d U V := by
  simp only [map_add, map_mul, nodeWord_omits x a b c d U hU, nodeWord_omits x a b c d V hV]
  simp [nodeWordMap, nodeWordImages, nodeValue, pencil]
theorem seedEval_nodeValue (q : ℕ) (x a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    seedEval q (nodeValue x a b c d U V) =
      (graph q U).eval (Polynomial.C x) * (Polynomial.C a + Polynomial.X * Polynomial.C b) +
      (graph q V).eval (Polynomial.C x) *
        (Polynomial.C c + Polynomial.X ^ q * Polynomial.C d) := by
  simp only [nodeValue, map_add, map_mul, ← eval_graph]
  simp [pencil, seedEval]
theorem parameterNode_nodeValue (x y a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    parameterNode y (nodeValue x a b c d U V) = nodeValue x a b c d U V := by
  have h : (parameterNode y).comp (parameterNode x) = parameterNode x := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [parameterNode]
  simp only [nodeValue, map_add, map_mul, ← AlgHom.comp_apply (parameterNode y) (parameterNode x), h]
  simp [pencil, parameterNode]
theorem degreeOf_parameterNode_le (j : Fin 5) (x : F) (Q : MvPolynomial (Fin 5) F) :
    (parameterNode x Q).degreeOf j ≤ Q.degreeOf j := by
  rw [← weightedTotalDegree_piSingle j (parameterNode x Q), ← weightedTotalDegree_piSingle j Q]
  apply weightedTotalDegree_aeval_le_of_le
  intro i
  rw [weightedTotalDegree_piSingle]
  fin_cases i <;> simp [Pi.single_apply, degreeOf_X, eq_comm]
theorem degreeOf_parameterNode_eq_zero (j : Fin 5) (x : F) (Q : MvPolynomial (Fin 5) F)
    (h3 : j ≠ 3) (h4 : j ≠ 4) : (parameterNode x Q).degreeOf j = 0 := by
  have h := weightedTotalDegree_aeval_le_of_le (fun _ : Fin 5 => 0) (Pi.single j 1)
    (![C x, 0, 0, MvPolynomial.X 3, MvPolynomial.X 4] : Fin 5 → MvPolynomial (Fin 5) F) Q (by
      intro i
      rw [weightedTotalDegree_piSingle]
      fin_cases i <;> simp [degreeOf_X, h3, h4])
  have hz : Q.weightedTotalDegree (fun _ => (0 : ℕ)) = 0 := by
    simp [weightedTotalDegree, Finsupp.weight_apply]
  rw [weightedTotalDegree_piSingle, hz] at h
  exact Nat.eq_zero_of_le_zero h
theorem degreeOf_pencil_le (i j : Fin 5) (a b : F) :
    (pencil j a b).degreeOf i ≤ if i = j then 1 else 0 := by
  refine (degreeOf_add_le i _ _).trans (max_le ?_ ?_)
  · simp
  · exact (degreeOf_mul_C_le (MvPolynomial.X j) i b).trans_eq (degreeOf_X i j)
theorem degreeOf_nodeValue_le (j : Fin 5) (x a b c d : F) (U V : MvPolynomial (Fin 5) F) :
    (nodeValue x a b c d U V).degreeOf j ≤
      if j = 3 then sWeight U V else if j = 4 then tWeight U V else 0 := by
  refine (degreeOf_add_le j _ _).trans (max_le ?_ ?_)
  · refine (degreeOf_mul_le j _ _).trans ?_
    have hp := degreeOf_pencil_le j 3 a b
    have hu := degreeOf_parameterNode_le j x U
    by_cases h3 : j = 3
    · subst j
      simp [sWeight] at hp hu ⊢
      omega
    by_cases h4 : j = 4
    · subst j
      simp [tWeight, h3] at hp hu ⊢
      omega
    rw [degreeOf_parameterNode_eq_zero j x U h3 h4]
    simpa [h3, h4] using hp
  · refine (degreeOf_mul_le j _ _).trans ?_
    have hp := degreeOf_pencil_le j 4 c d
    have hv := degreeOf_parameterNode_le j x V
    by_cases h3 : j = 3
    · subst j
      simp [sWeight] at hp hv ⊢
      omega
    by_cases h4 : j = 4
    · subst j
      simp [tWeight, h3] at hp hv ⊢
      omega
    rw [degreeOf_parameterNode_eq_zero j x V h3 h4]
    simpa [h3, h4] using hp
def liftCoordinate (f : Polynomial F) : MvPolynomial (Fin 5) F :=
  Polynomial.aeval (MvPolynomial.X 0) f
theorem parameterNode_liftCoordinate (x : F) (f : Polynomial F) :
    parameterNode x (liftCoordinate f) = C (f.eval x) := by
  rw [liftCoordinate, ← Polynomial.aeval_algHom_apply (parameterNode x)]
  simp only [parameterNode, aeval_X, Matrix.cons_val_zero, Polynomial.aeval_def, algebraMap_eq]
  exact Polynomial.eval₂_at_apply _ _
theorem degreeOf_liftCoordinate (j : Fin 5) (f : Polynomial F) :
    (liftCoordinate f).degreeOf j ≤ f.natDegree * (MvPolynomial.X 0 : MvPolynomial (Fin 5) F).degreeOf j := by
  rw [liftCoordinate, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun n hn => ?_)
  rw [algebraMap_eq]
  exact (degreeOf_C_mul_le _ j _).trans ((degreeOf_pow_le j _ n).trans
    (Nat.mul_le_mul_right _ (Polynomial.le_natDegree_of_mem_supp n hn)))
def interpolant {N : ℕ} (x : Fin N → F) (v : Fin N → MvPolynomial (Fin 5) F) :
    MvPolynomial (Fin 5) F :=
  ∑ i, liftCoordinate (Lagrange.basis Finset.univ x i) * v i
theorem parameterNode_interpolant {N : ℕ} (x : Fin N → F) (hx : Function.Injective x)
    (v : Fin N → MvPolynomial (Fin 5) F) (hv : ∀ i, parameterNode (x i) (v i) = v i)
    (j : Fin N) : parameterNode (x j) (interpolant x v) = v j := by
  rw [interpolant, map_sum]
  simp only [map_mul, parameterNode_liftCoordinate]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · rw [Lagrange.eval_basis_self hx.injOn (Finset.mem_univ j), map_one, one_mul, hv]
  · intro i _ hij
    rw [Lagrange.eval_basis_of_ne hij (Finset.mem_univ j), map_zero, zero_mul]
theorem degreeOf_interpolant_le {N : ℕ} (x : Fin N → F) (hx : Function.Injective x)
    (v : Fin N → MvPolynomial (Fin 5) F) (j : Fin 5) (b : ℕ)
    (hv : ∀ i, (v i).degreeOf j ≤ b) :
    (interpolant x v).degreeOf j ≤ (N - 1) * (MvPolynomial.X 0 : MvPolynomial (Fin 5) F).degreeOf j + b := by
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun i hi => ?_)
  have h := degreeOf_liftCoordinate j (Lagrange.basis Finset.univ x i)
  rw [Lagrange.natDegree_basis hx.injOn hi, Finset.card_univ, Fintype.card_fin] at h
  exact (degreeOf_mul_le j _ _).trans (Nat.add_le_add h (hv i))
end
end K1_11_2_2
end
section
namespace K1_14_3R_1
noncomputable section
open K1 K1_14 K1_14_3 K1_14_2_6_2
private theorem partial_commute (i j : Fin 4) :
    Function.Commute (coordDeriv i) (coordDeriv j) := by
  intro Q
  by_cases hij : i = j
  · subst j
    rfl
  apply MvPolynomial.ext
  intro d
  simp only [coordDeriv, MvPolynomial.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    ite_eq_right hij, ite_eq_right (Ne.symm hij), add_zero]
  rw [add_right_comm d (Finsupp.single i 1) (Finsupp.single j 1)]
  ring
theorem reverse_seed_contact {q : Surface} {P : Jet} {k : ℕ}
    {y v : SeedClosure} (hyv : OnSeedFibre q y v) (hk : k < p)
    (h : ∀ a b : ℕ, a + b < k → seedHasse 1 b (seedHasse 0 a P) ∈ q.asIdeal) :
    K1_14_2_6.HasSeedContact (RingHom.ker (K1_14_2_6.genericSeedPoint y v)) P k := by
  let T := K1_14_2.toJet
  let g := K1_14_2_6.genericSeedPoint y v
  have iter0 (r : ℕ) (Q : Jet) : (coordDeriv 0)^[r] (T Q) =
      r.factorial • T (seedHasse 0 r Q) := seed_iter 0 r Q
  have iter1 (r : ℕ) (Q : Jet) : (coordDeriv 1)^[r] (T Q) =
      r.factorial • T (seedHasse 1 r Q) := seed_iter 1 r Q
  have scale (i : Fin 4) (n r : ℕ) (Q : K1_14_2.Ambient) :
      (coordDeriv i)^[r] (n • Q) = n • (coordDeriv i)^[r] Q := by
    have hcomm : Function.Commute (coordDeriv i) (fun A : K1_14_2.Ambient => n • A) :=
      fun A => map_nsmul (MvPolynomial.pderiv (R := FX) i) n A
    exact (hcomm.iterate_left r) Q
  intro a b hab
  have hforward : T (seedHasse 1 b (seedHasse 0 a P)) ∈ RingHom.ker g := by
    change seedHasse 1 b (seedHasse 0 a P) ∈ (RingHom.ker g).comap T
    rw [seed_chart_ker hyv]
    exact h a b hab
  have hcomm := ((partial_commute 0 1).iterate_iterate a b) (T P)
  change (coordDeriv 0)^[a] ((coordDeriv 1)^[b] (T P)) =
    (coordDeriv 1)^[b] ((coordDeriv 0)^[a] (T P)) at hcomm
  have hleft : (coordDeriv 0)^[a] ((coordDeriv 1)^[b] (T P)) =
      b.factorial • a.factorial • T (seedHasse 0 a (seedHasse 1 b P)) := by
    rw [iter1, scale, iter0]
  have hright : (coordDeriv 1)^[b] ((coordDeriv 0)^[a] (T P)) =
      a.factorial • b.factorial • T (seedHasse 1 b (seedHasse 0 a P)) := by
    rw [iter0, scale, iter1]
  have he := congrArg g (hleft.symm.trans (hcomm.trans hright))
  simp only [map_nsmul, RingHom.mem_ker.mp hforward, nsmul_zero] at he
  let : CharP SeedClosure p :=
    charP_of_injective_ringHom (algebraMap K SeedClosure).injective p
  have hp := CharP.char_is_prime_of_two_le K p (by decide)
  have hfac (n : ℕ) (hn : n < p) : (n.factorial : SeedClosure) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hn)
      (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff SeedClosure p _).mp hz))
  simp only [nsmul_eq_mul] at he
  exact RingHom.mem_ker.mpr
    ((mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (hfac b (by omega)))).resolve_left
      (hfac a (by omega)))
theorem proof : K1_14_3R.c1 := by
  intro q P k hq hk hP y v hyv
  let I := RingHom.ker (K1_14_2_6.genericSeedPoint y v)
  have hjet : K1_14_2_6.HasJetContact P y v k :=
    K1_14_2_6_2.proof I (jet_chart hq hyv) P k hk (reverse_seed_contact hyv hk hP) y v rfl
  exact fibre_pow_of_hasse (fibreRow P) y v k hjet
end
end K1_14_3R_1
end
section
set_option autoImplicit false
namespace K1_13_7_2_3_1_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_2 K1_13_6_2_3 K1_13_7_1 K1_13_6_2_3_2 K1_13_6_2_3_2_5 Filter
private lemma deltas_sub {ι : Type} [DecidableEq ι] (used : List ι)
    (H G : (ι → ℕ) → ℚ) (a : ι → ℕ) :
    deltas used (fun b => H b - G b) a = deltas used H a - deltas used G a := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih]; ring
private lemma deltas_shift {ι : Type} [DecidableEq ι] (used : List ι)
    (H : (ι → ℕ) → ℚ) (a v : ι → ℕ) :
    deltas used (fun b => H (b + v)) a = deltas used H (a + v) := by
  induction used generalizing a with
  | nil => rfl
  | cons i rest ih => simp only [deltas, ih, add_right_comm a (step i) v]
private lemma eventually_shift {ι : Type} {Q : (ι → ℕ) → Prop} (v : ι → ℕ)
    (h : ∀ᶠ a in atTop, Q a) : ∀ᶠ a in atTop, Q (a + v) := by
  obtain ⟨u, hu⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨u, fun a ha => hu (a + v) (ha.trans (le_add_of_nonneg_right zero_le))⟩
private lemma spend {ι : Type} [DecidableEq ι] (used : List ι) (v : ι → ℕ)
    (B C G H : (ι → ℕ) → ℚ) (heq : ∀ a, B (a + v) + H a = G (a + v))
    (hpos : ∀ᶠ a in atTop, 0 ≤ deltas used (fun b => B b - C b) a) :
    ∀ᶠ a in atTop, deltas used C (a + v) ≤ deltas used G (a + v) - deltas used H a := by
  have hid : (fun a => B (a + v)) = fun a => G (a + v) - H a := by
    funext a
    linarith [heq a]
  filter_upwards [eventually_shift v hpos] with a ha
  rw [deltas_sub] at ha
  rw [← deltas_shift used B, hid, deltas_sub, deltas_shift] at ha
  linarith
private lemma graded_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (slot : σ → ι) :
    Graded slot (⊤ : Ideal (MvPolynomial σ GeoField)) := by
  intro f hf a
  exact Submodule.mem_top
private lemma hilbert_top {ι σ : Type} [DecidableEq ι] (slot : σ → ι) (a : ι → ℕ) :
    hilbert slot (⊤ : Ideal (MvPolynomial σ GeoField)) a = 0 := by
  have : Subsingleton (MvPolynomial σ GeoField ⧸ (⊤ : Ideal (MvPolynomial σ GeoField))) :=
    (Ideal.Quotient.subsingleton_iff).2 rfl
  simp [hilbert, Module.finrank_eq_zero_of_subsingleton]
theorem hilbert_difference
    {ι σ : Type} [Fintype ι] [DecidableEq ι] [Finite σ]
    (slot : σ → ι) (I K : Ideal (MvPolynomial σ GeoField))
    (hI : Graded slot I) (hK : Graded slot K) (hle : I ≤ K) :
    let H := fun a => hilbert slot I a - hilbert slot K a
    (∃ P : MvPolynomial ι ℚ, ∀ᶠ a in atTop, MvPolynomial.eval (fun i => (a i : ℚ)) P = H a) ∧
    ∀ used : List ι, ∀ᶠ a in atTop, 0 ≤ deltas used H a := by
  classical
  let _ := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  obtain ⟨A, hA⟩ := m.exists_finset_standardExponents_iff I
  obtain ⟨B, hB⟩ := m.exists_finset_standardExponents_iff K
  have hAB : outside B ⊆ outside A := by
    intro e he
    exact (hA e).mp (fun f hf => (hB e).mpr he f (hle hf))
  have eqI : hilbert slot I = sliceCount slot A := by
    funext a
    rw [standard_rank slot m I hI a]
    simp only [sliceCount, hA, outside, Set.mem_ofPred_eq]
  have eqK : hilbert slot K = sliceCount slot B := by
    funext a
    rw [standard_rank slot m K hK a]
    simp only [sliceCount, hB, outside, Set.mem_ofPred_eq]
  rw [eqI, eqK]
  exact K1_13_6_2_3_2_1.proof slot A B hAB
theorem eventually_deltas_cap_hilbert
    {ι : Type} [Fintype ι] [DecidableEq ι] (shapes : ι → Shape) (J : Ideal GeoJets)
    (base : ι) (used : List ι) (hsh : ∀ i, Chamber (shapes i))
    (hbase : ChamberBox (shapes base))
    (hn : used.Nodup) (hd : dimension J ≤ used.length) :
    ∀ᶠ a in atTop, deltas used (hilbert (capSlot shapes) (capIdeal shapes J)) a =
      polarize (capCoeff J used.length) (used.map shapes) (shapes base) := by
  let slot := capSlot shapes
  let I := capIdeal shapes J
  have hI := (K1_13_6_2_3_2_3.proof shapes J).1
  have hall := (hilbert_difference slot I ⊤ hI (graded_top slot) le_top).1
  rw [show (fun a => hilbert slot I a - hilbert slot ⊤ a) = hilbert slot I by
    funext a; simp [hilbert_top]] at hall
  obtain ⟨P, hP⟩ := hall
  have hrank : hilbert slot I = fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ) := by
    funext a
    rw [(K1_13_6_2_3_2_3.proof shapes J).2 a, product_eq_cap shapes hsh a]
  rw [hrank] at hP ⊢
  obtain ⟨u, hu⟩ := eventually_atTop.mp hP
  let K := fun a => (supportRank J (capExponents (shapeSum shapes a)) : ℚ)
  have hcompare (v : ι → ℕ) (hv : 0 < v base) :=
    ray_degree_and_coefficient shapes hsh J P u v (by
      change 0 < ∑ i, v i * (shapes i).t
      have hle := Finset.single_le_sum (f := fun i => v i * (shapes i).t)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ base)
      exact (Nat.mul_pos hv hbase.2.2).trans_le hle) hu _ hd
  have hdeg : P.totalDegree ≤ used.length :=
    totalDegree_le_of_ray_degree P u _ fun v hv => (hcompare v (hv base)).1
  let F := fun v : ι → ℕ =>
    MvPolynomial.eval (fun i => (v i : ℚ)) (MvPolynomial.homogeneousComponent used.length P)
  have hright := deltas_congr_on_upper used F
    (fun v => capCoeff J used.length (shapeSum shapes v)) (step base) fun v hv =>
      (ray_top P u v hdeg).symm.trans (hcompare v (by
        have h : step base base ≤ v base := hv base
        exact Nat.succ_le_iff.mp (by simpa [step] using h))).2
  filter_upwards [eventually_ge_atTop u] with a ha
  change deltas used K a = _
  calc
    _ = deltas used (fun v => MvPolynomial.eval (fun i => (v i : ℚ)) P) a :=
      deltas_congr_on_upper used K _ a fun v hv => (hu v (ha.trans hv)).symm
    _ = deltas used F (step base) := deltas_top used hn P hdeg a (step base)
    _ = _ := by rw [hright, deltas_shapeSum, shapeSum_step]
theorem proof :
    K1_13_7_2_3_1.c1 := by
  classical
  intro J p boxes hp hboxes _ hdim D hD hreg
  let ι := Option (Option (Fin boxes.length))
  let base : ι := none
  let i : ι := some none
  let emb : Fin boxes.length → ι := fun k => some (some k)
  let rest := (List.finRange boxes.length).map emb
  let shapes : ι → Shape
    | none => ⟨3, 3, 1⟩
    | some none => p
    | some (some k) => boxes.get k
  have hsh (k : ι) : Chamber (shapes k) := by
    cases k with
    | none =>
      change Chamber ⟨3, 3, 1⟩
      exact ⟨by decide, by decide⟩
    | some k => cases k with
      | none => exact hp
      | some k => exact hboxes _ (List.get_mem _ _)
  have hbaseBox : ChamberBox (shapes base) := by
    change ChamberBox (⟨3, 3, 1⟩ : Shape)
    exact ⟨by decide, by decide, by decide⟩
  have hi : i ∉ rest := by
    intro h
    obtain ⟨k, _, hk⟩ := List.mem_map.mp h
    change (some (some k) : Option (Option (Fin boxes.length))) = some none at hk
    have hinner : (some k : Option (Fin boxes.length)) = none := Option.some.inj hk
    cases hinner
  have hn : rest.Nodup := (List.nodup_finRange _).map
    (fun _ _ h => Option.some.inj (Option.some.inj h))
  have hn' : (i :: rest).Nodup := List.nodup_cons.mpr ⟨hi, hn⟩
  have hmap : rest.map shapes = boxes := by
    simp [rest, List.map_map, Function.comp_def, emb, shapes]
  have hlen : rest.length = boxes.length := by simp [rest]
  let slot := capSlot shapes
  let I := capIdeal shapes J
  let I₁ := capIdeal shapes (cut J D)
  let I₂ := capIdeal shapes (cut J (D ^ 2))
  have hgraded₂ := (K1_13_6_2_3_2_3.proof shapes (cut J (D ^ 2))).1
  obtain ⟨B, C, hB, hC, hBI, hCI, heqB, heqC⟩ :=
    K1_13_6_2_3_2_6.proof shapes i J D hD hreg (K1_13_6_2_3_2_3.proof shapes J).1 hgraded₂
  have hposB := (hilbert_difference slot B I₂ hB hgraded₂ hBI).2 rest
  have hposC := (hilbert_difference slot C I₁ hC (K1_13_6_2_3_2_3.proof shapes (cut J D)).1 hCI).2 rest
  have hspendB := spend rest (step i) (hilbert slot B) (hilbert slot I₂) (hilbert slot I)
    (hilbert slot I) heqB hposB
  have hspendC := spend rest (step i) (hilbert slot C) (hilbert slot I₁) (hilbert slot I₂)
    (hilbert slot I₁) heqC hposC
  have hd₁ : dimension (cut J D) ≤ rest.length := by
    have hdrop : dimension (cut J D) ≤ dimension J - 1 := cut_dimension hreg
    omega
  have hd₀ : dimension J ≤ (i :: rest).length := by simpa [hlen] using hdim
  have hr₀ := eventually_deltas_cap_hilbert shapes J base (i :: rest) hsh hbaseBox hn' hd₀
  have hr₁ := eventually_deltas_cap_hilbert shapes (cut J D) base rest hsh hbaseBox hn hd₁
  have hfinal : ∀ᶠ _a in (atTop : Filter (ι → ℕ)),
      2 * polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ ≤
        polarize (capCoeff J (p :: boxes).length) (p :: boxes) ⟨3, 3, 1⟩ := by
    filter_upwards [hspendB, hspendC, hr₀, hr₁, eventually_shift (step i) hr₁] with a hb hc h₀ h₁ h₁'
    rw [List.map_cons, hmap, List.length_cons, hlen] at h₀
    rw [hlen, hmap] at h₁ h₁'
    change deltas rest (hilbert slot I) (a + step i) - deltas rest (hilbert slot I) a =
      polarize (capCoeff J (boxes.length + 1)) (p :: boxes) ⟨3, 3, 1⟩ at h₀
    change deltas rest (hilbert slot I₁) a =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁
    change deltas rest (hilbert slot I₁) (a + step i) =
      polarize (capCoeff (cut J D) boxes.length) boxes ⟨3, 3, 1⟩ at h₁'
    simp only [List.length_cons]
    linarith [hb, hc, h₀, h₁, h₁']
  obtain ⟨_, hfinal⟩ := hfinal.exists
  unfold mixedDegree
  rw [List.length_cons, pow_succ, mul_comm ((2 : ℚ)^boxes.length) 2, ← div_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).2 (by simpa [mul_comm] using hfinal)
end
end K1_13_7_2_3_1_1
end
