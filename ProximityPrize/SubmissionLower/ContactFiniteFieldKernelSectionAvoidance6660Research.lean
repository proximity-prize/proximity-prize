import ProximityPrize.Benchmark.TargetLower

 













namespace ProximityPrize.SubmissionLower
namespace ContactFiniteFieldKernelSectionAvoidance6660Research

open Function Set

set_option autoImplicit false

noncomputable section

variable {Factor K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem finite_iUnion_ssubset
    (s : Finset Factor) (p : Factor → Submodule K V)
    (h₁ : ∀ i, p i ≠ ⊤) (h₂ : s.card < ENat.card K) :
    ⋃ i ∈ s, (p i : Set V) ⊂ univ := by
  letI : DecidableEq Factor := Classical.decEq Factor
  letI : DecidableEq K := Classical.decEq K
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hj' =>
    simp only [ssubset_univ_iff] at hj' ⊢
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using! h₁ j
    replace h₂ : s.card + 1 < ENat.card K := by
      simpa [Finset.card_insert_of_notMem hj] using! h₂
    specialize hj' (lt_trans ENat.natCast_lt_succ h₂)
    contrapose hj'
    replace hj' : (p j : Set V) ∪ (⋃ i ∈ s, p i) = univ := by
      simpa [Finset.mem_insert] using! hj'
    suffices (p j : Set V) ⊆ ⋃ i ∈ s, p i by
      rwa [union_eq_right.mpr this] at hj'
    intro x (hx : x ∈ p j)
    rcases eq_or_ne x 0 with rfl | hx₀
    · simpa using! hs
    obtain ⟨y, hy⟩ : ∃ y, y ∉ p j := by
      specialize h₁ j
      contrapose! h₁
      ext
      simp [h₁]
    have hy₀ : y ≠ 0 := by aesop
    let sxy := {x + t • y | (t : K) (ht : t ≠ 0)}
    have hsxy : sxy ⊆ ⋃ i ∈ s, p i := by
      suffices Disjoint sxy (p j) from
        this.subset_right_of_subset_union <| hj' ▸ sxy.subset_univ
      rw [Set.disjoint_iff]
      rintro - ⟨⟨t, ht₀, rfl⟩, ht : x + t • y ∈ p j⟩
      rw [(p j).add_mem_iff_right hx, (p j).smul_mem_iff ht₀] at ht
      contradiction
    obtain ⟨k, hk, t₁, t₂, ht, ht₁, ht₂⟩ :
        ∃ᵉ (k ∈ s) (t₁ : K) (t₂ : K),
          t₁ ≠ t₂ ∧ x + t₁ • y ∈ p k ∧ x + t₂ • y ∈ p k := by
      suffices ∃ᵉ (k ∈ s) (z₁ ∈ sxy) (z₂ ∈ sxy),
          z₁ ≠ z₂ ∧ z₁ ∈ p k ∧ z₂ ∈ p k by
        obtain ⟨k, hk, -, ⟨t₁, -, rfl⟩, -, ⟨t₂, -, rfl⟩,
          htne, ht₁, ht₂⟩ := this
        exact ⟨k, hk, t₁, t₂, by aesop, ht₁, ht₂⟩
      choose f hf using fun z : sxy ↦ mem_iUnion.mp (hsxy z.property)
      have hf' : MapsTo f univ s := fun z _ ↦ by
        specialize hf z
        aesop
      suffices ∃ z₁ z₂, z₁ ≠ z₂ ∧ f z₁ = f z₂ by
        obtain ⟨z₁, z₂, hne, heq⟩ := this
        exact ⟨f z₁, hf' (mem_univ _), z₁, z₁.property, z₂, z₂.property,
          Subtype.coe_ne_coe.mpr hne, by specialize hf z₁; simp_all,
          by specialize hf z₂; aesop⟩
      have key : s.card < sxy.encard := by
        refine lt_of_add_lt_add_right <| lt_of_lt_of_le h₂ ?_
        have hinj : Injective (fun t : K ↦ x + t • y) :=
          fun t₁ t₂ ht ↦ smul_left_injective K hy₀ <| by simpa using! ht
        have aux : sxy =
            ((fun t : K ↦ x + t • y) '' {t | t ≠ 0}) := by
          ext
          simp [sxy]
        rw [aux, hinj.encard_image, encard_ne_add_one]
      obtain ⟨z₁, -, z₂, -, h⟩ :=
        exists_ne_map_eq_of_encard_lt_of_maps_to (by simpa) hf'
      exact ⟨z₁, z₂, h⟩
    replace ht : y ∈ p k := by
      have : (t₁ - t₂) • y ∈ p k := by
        convert sub_mem ht₁ ht₂
        all_goals module
      refine ((p k).smul_mem_iff ?_).mp this
      rwa [sub_ne_zero]
    replace ht : x ∈ p k := by
      convert sub_mem ht₁ ((p k).smul_mem t₁ ht)
      simp
    simpa using! ⟨k, hk, ht⟩

 

theorem exists_section_avoiding_bounded_proper_submodules
    [Fintype Factor]
    (bad : Factor → Submodule K V)
    (hproper : ∀ f, bad f ≠ ⊤)
    (hcard : Fintype.card Factor < ENat.card K) :
    ∃ v : V, ∀ f, v ∉ bad f := by
  classical
  suffices ⋃ f, (bad f : Set V) ⊂ univ by
    simpa [ssubset_univ_iff, iUnion_eq_univ_iff] using this
  simpa using finite_iUnion_ssubset
    (Finset.univ : Finset Factor) bad hproper (by simpa using hcard)

 

theorem row6660_factor_avoidance_numeric_gate :
    717 < 2130706433 := by
  norm_num

end


end ContactFiniteFieldKernelSectionAvoidance6660Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactFiniteFieldKernelSectionAvoidance6660Research.exists_section_avoiding_bounded_proper_submodules
#print axioms ProximityPrize.SubmissionLower.ContactFiniteFieldKernelSectionAvoidance6660Research.row6660_factor_avoidance_numeric_gate
