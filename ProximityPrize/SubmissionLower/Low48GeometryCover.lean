import ProximityPrize.SubmissionLower.Low48Price

set_option Elab.async false
namespace Low48GeometryLead
open K1_13 (Geom Row shape indexDegree)
open K1_13_1 (topView topView_degree anchorLead anchorLead_ne indexDegree_eq)
open MvPolynomial
open scoped Polynomial

/-- Taking the coefficient of the highest power of the last variable removes
that power from every weighted degree of its supporting monomials. -/
theorem term_weight (P : Row 4) (m : Fin 3 →₀ ℕ) (hm : m ∈ (anchorLead P).support) :
    ∃ u ∈ P.support, ∀ w : Fin 4 → ℕ,
      m.weight (fun i => w i.castSucc) + (shape P).t * w 3 = u.weight w := by
  classical
  let k := (topView P).natDegree
  let c := rename finSuccEquivLast P
  have hc : c.coeff (m.optionElim k) = (anchorLead P).coeff m :=
    (optionEquivLeft_coeff_coeff _ _ _ _).symm
  have hs : m.optionElim k ∈ c.support :=
    mem_support_iff.mpr (by rw [hc]; exact mem_support_iff.mp hm)
  rw [show c = rename finSuccEquivLast P from rfl,
    support_rename_of_injective finSuccEquivLast.injective] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hs
  refine ⟨u, hu, fun w => ?_⟩
  let w' : Option (Fin 3) → ℕ := fun v => v.elim (w 3) (fun i => w i.castSucc)
  have hlast : finSuccEquivLast (3 : Fin 4) = none := finSuccEquivLast_last
  have hw : ∀ i : Fin 4, w' (finSuccEquivLast i) = w i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [w', hlast, show Fin.last 3 = (3 : Fin 4) by rfl]
    · simp [w']
  have hweight : (m.optionElim k).weight w' = u.weight w := by
    rw [← he]
    simp only [Finsupp.weight_apply, smul_eq_mul]
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; rw [Nat.add_mul])]
    simp only [hw]
  rw [Finsupp.weight_optionElim] at hweight
  simpa only [w', Option.elim, k, topView_degree, smul_eq_mul, Nat.add_comm, Nat.mul_comm] using hweight

theorem lead_degree (P : Row 4) (hP : P ≠ 0) :
    (anchorLead P).totalDegree + (shape P).t ≤ P.totalDegree := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ ((support_nonempty.mpr (anchorLead_ne hP))) (fun m => m.weight (1 : Fin 3 → ℕ))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  have h := (hw (1 : Fin 4 → ℕ)).le.trans (le_weightedTotalDegree _ hu)
  rw [← weightedTotalDegree_one, weightedTotalDegree, he, ← weightedTotalDegree_one]
  have hconst : (fun i : Fin 3 => (1 : Fin 4 → ℕ) i.castSucc) = (1 : Fin 3 → ℕ) := rfl
  rw [hconst] at h
  simpa only [Pi.one_apply, Nat.mul_one] using h

theorem lead_index (P : Row 4) (hP : P ≠ 0) :
    indexDegree (anchorLead P) + 3 * (shape P).t ≤ indexDegree P := by
  classical
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup _ (support_nonempty.mpr (anchorLead_ne hP)) (fun m => m.weight (fun i : Fin 3 => i.val))
  obtain ⟨u, hu, hw⟩ := term_weight P m hm
  rw [indexDegree_eq, weightedTotalDegree, he, indexDegree_eq]
  simpa [Nat.mul_comm] using (hw (fun i => i.val)).le.trans (le_weightedTotalDegree _ hu)

end Low48GeometryLead

namespace Low48GeometryCover
noncomputable section
open Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
open P3 (K I node)
open Low48Price (TrueWeightLE anchorCutoff physicalDegree fullCap Fits LowerRow SmallFactor)
open K1_13 (Geom embed extend Row shape InBox atJet indexDegree jet OnFactor)
open K1_13_1 (anchorLead anchorLead_ne anchorLead_mul indexDegree_eq eval_anchorLead
  atJet_eq_anchorLead_of_top_zero)
open scoped BigOperators Polynomial
open private coeff_flatten anchorLead_term index_bounds from ProximityPrize.SubmissionLower.Fast040

structure Cover (top : ℕ) {n : ℕ} (Γ : Finset K) (s : K → K[X])
    (g : Row 3) (f : Fin n → Row 4) : Prop where
  lower : LowerRow top g
  factors : ∀ i, SmallFactor (f i)
  different : ∀ i j, i ≠ j → ¬ Associated (f i) (f j)
  fits : Fits top (fun i => shape (f i))
  covers : ∀ γ ∈ Γ, K1_13.atJet g (extend (s γ)) = 0 ∨
    ∃ i, K1_13.OnFactor (f i) (extend (s γ))
theorem trueWeight_iff {n D : ℕ} (P : Row n) :
    TrueWeightLE P D ↔
      ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).weightedTotalDegree
        (fun v => v.elim 1 (fun i => physicalDegree - i.val)) ≤ D := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  constructor
  · intro h u hu
    have hc : (P.coeff u.some).coeff (u none) ≠ 0 := by
      rw [← coeff_flatten, Finsupp.optionElim_some]
      exact MvPolynomial.mem_support_iff.mp hu
    have hm : u.some ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (fun hz => hc (by simp [hz]))
    have hi := Polynomial.le_natDegree_of_ne_zero hc
    rw [← Finsupp.optionElim_some u, Finsupp.weight_optionElim, one_mul]
    apply (Nat.add_le_add_right hi _).trans
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using h _ hm
  · intro h m hm
    let d := (P.coeff m).natDegree
    have hc : (P.coeff m).coeff d ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hm)
    have hu : m.optionElim d ∈ ((MvPolynomial.optionEquivRight Geom (Fin n)).symm P).support :=
      MvPolynomial.mem_support_iff.mpr (by rwa [coeff_flatten])
    have hb := h _ hu
    rw [Finsupp.weight_optionElim, one_mul] at hb
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm] using hb
theorem differentialWeight_eq : differentialWeight (d := 3) physicalDegree =
    fun v => v.elim 1 (fun i => physicalDegree - i.val) := by
  funext v
  cases v <;> rfl
section FactorCover
open MvPolynomial UniqueFactorizationMonoid
private theorem lower_of_anchor (P : Row 4) (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨123, 50, 13⟩) (hw : TrueWeightLE P anchorCutoff) :
    LowerRow (shape P).t (anchorLead P) := by
  refine ⟨anchorLead_ne hP, ?_, ?_, ?_⟩
  · have hb := (Low48GeometryLead.lead_degree P hP).trans hbox.1
    change (anchorLead P).totalDegree + (shape P).t ≤ 123 at hb
    change (anchorLead P).totalDegree ≤ 123 - (shape P).t
    omega
  · have hj := (Low48GeometryLead.lead_index P hP).trans hbox.2.1
    change indexDegree (anchorLead P) + 3 * (shape P).t ≤ 50 at hj
    change indexDegree (anchorLead P) ≤ 50 - 3 * (shape P).t
    omega
  · intro m hm
    obtain ⟨u, hu, hc, h⟩ := anchorLead_term P m hm
    have hle := h (fun i => physicalDegree - i.val)
    rw [← hc]
    apply (Nat.add_le_add_left _ _).trans (hw u hu)
    simpa only [Finsupp.weight_apply, smul_eq_mul, Nat.mul_comm, Fin.val_castSucc] using hle
private theorem factor_small {P f : Row 4} (hP : P ≠ 0)
    (hbox : InBox (shape P) ⟨123, 50, 13⟩) (hw : TrueWeightLE P anchorCutoff)
    (hf : Irreducible f) (ht : 0 < (shape f).t) (hd : f ∣ P) : SmallFactor f := by
  refine ⟨hf, ht, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h := weightedTotalDegree_le_of_dvd (1 : Fin 4 → ℕ) hd hP
    rw [weightedTotalDegree_one, weightedTotalDegree_one] at h
    exact h.trans hbox.1
  · have h := weightedTotalDegree_le_of_dvd (fun i => i.val) hd hP
    rw [← indexDegree_eq, ← indexDegree_eq] at h
    exact h.trans hbox.2.1
  · have h := weightedTotalDegree_le_of_dvd (Pi.single (3 : Fin 4) 1) hd hP
    simp only [weightedTotalDegree_piSingle] at h
    exact h.trans hbox.2.2
  · let e := MvPolynomial.optionEquivRight Geom (Fin 4)
    have hd' : e.symm f ∣ e.symm P := _root_.map_dvd e.symm hd
    have hP' : e.symm P ≠ 0 := fun h => hP (e.symm.injective (h.trans (map_zero _).symm))
    exact (trueWeight_iff f).mpr
      ((weightedTotalDegree_le_of_dvd _ hd' hP').trans ((trueWeight_iff P).mp hw))
theorem cover_of_anchor {Γ : Finset K} {s : K → K[X]} (P : Row 4)
    (hP : P ≠ 0) (hbox : InBox (shape P) ⟨123, 50, 13⟩)
    (hw : TrueWeightLE P anchorCutoff)
    (hz : ∀ γ ∈ Γ, atJet P (extend (s γ)) = 0) :
    ∃ (top : ℕ) (n : ℕ) (g : Row 3) (f : Fin n → Row 4), top ≤ 13 ∧ Cover top Γ s g f := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT : ∀ q ∈ T, q ∈ A ∧ 0 < (shape q).t := by
    intro q hq
    simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  have hd : (∏ i, f i) ∣ P := by
    have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  have fit : Fits (shape P).t (fun i => shape (f i)) := by
    refine ⟨fun i => ⟨(hfi i).2, index_bounds (f i)⟩, ?_, ?_, ?_⟩
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (1 : Fin 4 → ℕ) Finset.univ f hP hd
      simp only [weightedTotalDegree_one] at h
      exact h.trans hbox.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (fun i => i.val) Finset.univ f hP hd
      simp only [← indexDegree_eq] at h
      exact h.trans hbox.2.1
    · have h := sum_weightedTotalDegree_le_of_prod_dvd (Pi.single (3 : Fin 4) 1) Finset.univ f hP hd
      simp only [weightedTotalDegree_piSingle] at h
      exact h
  refine ⟨(shape P).t, n, anchorLead P, f, hbox.2.2, ⟨lower_of_anchor P hP hbox hw, ?_, ?_, fit, ?_⟩⟩
  · intro i
    exact factor_small hP hbox hw (irreducible_of_normalized_factor _ (hfi i).1)
      (hfi i).2 (dvd_of_mem_normalizedFactors (hfi i).1)
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · intro γ hγ
    let S := extend (s γ)
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : MvPolynomial.eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ MvPolynomial.eval (jet S) A.prod at hdiv
      rw [hz γ hγ, zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hSA
    obtain ⟨q, hq, hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R, hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR, anchorLead_mul, atJet, map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq, hqt⟩
    let j := e.symm ⟨q, hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hqT⟩)
    exact ⟨j, by rw [hj, OnFactor, ← eval_anchorLead]; exact ⟨hqS, hqlead⟩⟩
end FactorCover

#print axioms cover_of_anchor
end
end Low48GeometryCover
