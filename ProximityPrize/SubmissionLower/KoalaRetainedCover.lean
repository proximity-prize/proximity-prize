import ProximityPrize.SubmissionLower.KoalaRetainedWitness

set_option autoImplicit false
set_option Elab.async false
namespace KoalaRetainedCut
noncomputable section

open P3 (K)
open K1_13 (Geom Row shape topLead atJet jet extend OnFactor)
open K1_13_1 (anchorLead anchorLead_mul eval_anchorLead atJet_eq_anchorLead_of_top_zero)
open UniqueFactorizationMonoid MvPolynomial
open scoped Polynomial BigOperators

/-- Canonical positive-top factors of any anchor, including the divisibility information used to assign marks. -/
theorem anchor_factors {P : Row 4} (hP : P ≠ 0) :
    ∃ (n : ℕ) (f : Fin n → Row 4),
      (∀ i, Irreducible (f i) ∧ 0 < (shape (f i)).t ∧ f i ∣ P) ∧
      (∀ i j, i ≠ j → ¬ Associated (f i) (f j)) ∧ (∏ i, f i) ∣ P ∧
      ∀ S : (Polynomial Geom), atJet P S = 0 → atJet (anchorLead P) S = 0 ∨ ∃ i, OnFactor (f i) S := by
  classical
  let _ : StrongNormalizationMonoid (Row 4) := UniqueFactorizationMonoid.strongNormalizationMonoid
  let A := normalizedFactors P
  let T := A.toFinset.filter fun q => 0 < (shape q).t
  let n := Fintype.card ↥T
  let e : Fin n ≃ ↥T := (Fintype.equivFin ↥T).symm
  let f : Fin n → Row 4 := fun i => (e i).val
  have hT (q) (hq : q ∈ T) : q ∈ A ∧ 0 < (shape q).t := by simpa [T] using hq
  have hfi (i : Fin n) : f i ∈ A ∧ 0 < (shape (f i)).t := hT _ (e i).property
  refine ⟨n,f,fun i => ⟨irreducible_of_normalized_factor _ (hfi i).1,(hfi i).2,
    dvd_of_mem_normalizedFactors (hfi i).1⟩,?_,?_,?_⟩
  · intro i j hij hassoc
    apply hij
    apply e.injective
    exact Subtype.ext (mem_normalizedFactors_eq_of_associated (hfi i).1 (hfi j).1 hassoc)
  · have heq : (∏ i, f i) = ∏ q ∈ T, q := by
      rw [show (∏ i, f i) = ∏ q : ↥T, q.val from e.prod_comp Subtype.val]
      exact Finset.prod_coe_sort T id
    rw [heq]
    exact ((Finset.prod_dvd_prod_of_subset T A.toFinset id (Finset.filter_subset _ _)).trans
      (Multiset.toFinset_prod_dvd_prod A)).trans (prod_normalizedFactors hP).dvd
  · intro S hz
    by_cases hg : atJet (anchorLead P) S = 0
    · exact Or.inl hg
    right
    have hSA : MvPolynomial.eval (jet S) A.prod = 0 := by
      have hdiv := _root_.map_dvd (MvPolynomial.eval (jet S)) (prod_normalizedFactors hP).symm.dvd
      change atJet P S ∣ MvPolynomial.eval (jet S) A.prod at hdiv
      rw [hz,zero_dvd_iff] at hdiv
      exact hdiv
    rw [map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hSA
    obtain ⟨q,hq,hqS⟩ := hSA
    have hqlead : atJet (anchorLead q) S ≠ 0 := by
      intro hzero
      obtain ⟨R,hR⟩ := dvd_of_mem_normalizedFactors hq
      apply hg
      rw [hR,anchorLead_mul,atJet,map_mul]
      exact mul_eq_zero_of_left hzero _
    have hqt : 0 < (shape q).t := by
      by_contra! h
      apply hqlead
      rw [← atJet_eq_anchorLead_of_top_zero q S (Nat.eq_zero_of_le_zero h)]
      exact hqS
    have hqT : q ∈ T := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hq,hqt⟩
    let j := e.symm ⟨q,hqT⟩
    have hj : f j = q := congrArg Subtype.val (e.apply_symm_apply ⟨q,hqT⟩)
    exact ⟨j,by rw [hj,OnFactor,← eval_anchorLead]; exact ⟨hqS,hqlead⟩⟩

theorem topLead_off_lower {P f : Row 4} {S : (Polynomial Geom)} (h : f ∣ P)
    (hoff : atJet (anchorLead P) S ≠ 0) : topLead f S ≠ 0 := by
  obtain ⟨G,rfl⟩ := h
  rw [anchorLead_mul,atJet,map_mul] at hoff
  rw [← eval_anchorLead]
  exact left_ne_zero_of_mul hoff

/-- Charge the lower leading coefficient first, then all retained factors. Every other mark is off the retained product. -/
theorem priority_pieces {n : ℕ} {P : Row 4} {f : Fin n → Row 4} (hdiv : ∀ i, f i ∣ P)
    {Γ : Finset K} (s : K → (Polynomial K)) (book : Finset K) (z : Finset (Fin n))
    (hbase : ∀ γ ∈ Γ, atJet (anchorLead P) (extend (s γ)) = 0 ∨ ∃ i, OnFactor (f i) (extend (s γ))) :
    ∃ (low : Finset K) (piece : Fin n → Finset K),
      low ⊆ Γ ∧ (∀ γ ∈ low, atJet (anchorLead P) (extend (s γ)) = 0) ∧
      (∀ i, piece i ⊆ Γ) ∧ (∀ i γ, γ ∈ piece i → γ ∉ book ∧ OnFactor (f i) (extend (s γ))) ∧
      (∀ i ∉ z, ∀ γ ∈ piece i, atJet (∏ j ∈ z, f j) (extend (s γ)) ≠ 0) ∧
      Γ.card ≤ book.card + low.card + ∑ i, (piece i).card := by
  classical
  let S (γ : K) := extend (s γ)
  let H := ∏ j ∈ z, f j
  let low := Γ.filter (fun γ => atJet (anchorLead P) (S γ)=0)
  let piece (i : Fin n) := Γ.filter (fun γ => γ∉book ∧ OnFactor (f i) (S γ) ∧
    (i∈z ∨ atJet H (S γ) ≠ 0))
  refine ⟨low,piece,Finset.filter_subset _ _,fun γ h => (Finset.mem_filter.mp h).2,
    fun i => Finset.filter_subset _ _,fun i _ h => ⟨(Finset.mem_filter.mp h).2.1,
      (Finset.mem_filter.mp h).2.2.1⟩,fun i hi _ h => (Finset.mem_filter.mp h).2.2.2.resolve_left hi,?_⟩
  have full : Γ ⊆ book ∪ low ∪ Finset.univ.biUnion piece := by
    intro γ hγ
    by_cases hb : γ∈book
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hb)
    by_cases hg : atJet (anchorLead P) (S γ)=0
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ,hg⟩))
    apply Finset.mem_union_right
    by_cases hH : atJet H (S γ)=0
    · have hp : ∏ j∈z, atJet (f j) (S γ) = 0 := by
        simpa only [H,atJet,map_prod] using hH
      obtain ⟨i,hi,hzero⟩ := Finset.prod_eq_zero_iff.mp hp
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,⟨hzero,topLead_off_lower (hdiv i) hg⟩,Or.inl hi⟩⟩
    · obtain ⟨i,hon⟩ := (hbase γ hγ).resolve_left hg
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr
        ⟨hγ,hb,hon,Or.inr hH⟩⟩
  exact (Finset.card_le_card full).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le))

#print axioms anchor_factors
#print axioms priority_pieces

end
end KoalaRetainedCut
