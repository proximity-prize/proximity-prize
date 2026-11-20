import ProximityPrize.SubmissionLower.Koala6844NormalizationCenter
import ProximityPrize.SubmissionLower.Koala6844NormalizationPrelude


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

private theorem topCoefficients_ne_both_zero {A : Fin 2 → Polynomial K}
    (hA : IsCoprime (A 0) (A 1)) :
    (A 0).coeff (affineDegree A) ≠ 0 ∨ (A 1).coeff (affineDegree A) ≠ 0 := by
  let a := affineDegree A
  by_contra h
  push Not at h
  have hlead0 : (A 0).natDegree = a → A 0 = 0 := by
    intro hdeg
    apply leadingCoeff_eq_zero.mp
    change (A 0).coeff (A 0).natDegree = 0
    simpa only [hdeg] using h.1
  have hlead1 : (A 1).natDegree = a → A 1 = 0 := by
    intro hdeg
    apply leadingCoeff_eq_zero.mp
    change (A 1).coeff (A 1).natDegree = 0
    simpa only [hdeg] using h.2
  obtain ⟨s, t, hst⟩ := hA
  unfold a affineDegree at hlead0 hlead1
  rcases le_total (A 0).natDegree (A 1).natDegree with he | he
  · have h1 : A 1 = 0 := hlead1 (max_eq_right he).symm
    have hdeg1 : (A 1).natDegree = 0 := by simp [h1]
    have h0 : A 0 = 0 := hlead0 (max_eq_left
      (show (A 1).natDegree ≤ (A 0).natDegree by omega)).symm
    simp [h0, h1] at hst
  · have h0 : A 0 = 0 := hlead0 (max_eq_left he).symm
    have hdeg0 : (A 0).natDegree = 0 := by simp [h0]
    have h1 : A 1 = 0 := hlead1 (max_eq_right
      (show (A 0).natDegree ≤ (A 1).natDegree by omega)).symm
    simp [h0, h1] at hst

theorem at_most_one_top_coefficient_zero (A : Fin 2 → Polynomial K)
    (hA : IsCoprime (A 0) (A 1)) (seeds : Finset K) :
    letI := Classical.decEq K
    (seeds.filter fun g => (specializeAffine A g).coeff (affineDegree A) = 0).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro g hg h hh
  have hg0 := (Finset.mem_filter.mp hg).2
  have hh0 := (Finset.mem_filter.mp hh).2
  simp only [specializeAffine, coeff_add, coeff_C_mul] at hg0 hh0
  by_cases hz : (A 1).coeff (affineDegree A) = 0
  · rw [hz, mul_zero, add_zero] at hg0
    exact ((topCoefficients_ne_both_zero hA).elim (fun h => h hg0) (fun h => h hz)).elim
  · apply mul_right_cancel₀ hz
    linear_combination hg0 - hh0

theorem specializeAffine_map (σ : K →+* K) (A : Fin 2 → Polynomial K) (g : K) :
    (specializeAffine A g).map σ =
      specializeAffine (fun j => (A j).map σ) (σ g) := by
  simp only [specializeAffine, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]

theorem exists_virtual_coprime_seeds (σ : K ≃+* K) (A : Fin 2 → Polynomial K)
    (d0 d1 : Polynomial K) (hd0 : d0 ≠ 0) (hd1 : d1 ≠ 0)
    (hA : IsCoprime (A 0) (A 1)) (seeds : Finset K) :
    ∃ retained ⊆ seeds,
      seeds.card ≤ retained.card + (1 + d0.natDegree + d1.natDegree) ∧
      ∀ g ∈ retained,
        (specializeAffine A g).natDegree = affineDegree A ∧
        IsCoprime (specializeAffine A g) d0 ∧
        IsCoprime ((specializeAffine A g).map σ.toRingHom) d1 := by
  classical
  let full (g : K) := (specializeAffine A g).coeff (affineDegree A) ≠ 0
  let d0ok (g : K) := IsCoprime (specializeAffine A g) d0
  let d1ok (g : K) := IsCoprime ((specializeAffine A g).map σ.toRingHom) d1
  let keep (g : K) := full g ∧ d0ok g ∧ d1ok g
  let retained := seeds.filter keep
  let dropD := seeds.filter fun g => ¬ full g
  let drop0 := seeds.filter fun g => ¬ d0ok g
  let drop1 := seeds.filter fun g => ¬ d1ok g
  have hhD : dropD.card ≤ 1 := by
    simpa only [dropD, full, ne_eq, not_not] using at_most_one_top_coefficient_zero A hA seeds
  have hh0 : drop0.card ≤ d0.natDegree :=
    Koala6844Moving.noncoprime_fixed_content_card_le (A 0) (A 1) d0 hA hd0 drop0
      (fun g hg => (Finset.mem_filter.mp hg).2)
  have hMapA : IsCoprime ((A 0).map σ.toRingHom) ((A 1).map σ.toRingHom) :=
    hA.map (mapRingHom σ.toRingHom)
  have hh1' : (drop1.image σ).card ≤ d1.natDegree := by
    apply Koala6844Moving.noncoprime_fixed_content_card_le _ _ _ hMapA hd1
    intro g hg
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp hg
    have hbad : ¬ IsCoprime ((specializeAffine A g').map σ.toRingHom) d1 :=
      (Finset.mem_filter.mp hg').2
    rw [specializeAffine_map] at hbad
    exact hbad
  have hh1 : drop1.card ≤ d1.natDegree := by
    rw [Finset.card_image_of_injective _ σ.injective] at hh1'
    exact hh1'
  have hcover : seeds.filter (fun g => ¬ keep g) ⊆ dropD ∪ drop0 ∪ drop1 := by
    intro g hg
    obtain ⟨hseed, hnot⟩ := Finset.mem_filter.mp hg
    by_cases hD : full g
    · by_cases h0 : d0ok g
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hseed, fun h1 => hnot ⟨hD, h0, h1⟩⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hseed, h0⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hseed, hD⟩))
  have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le (dropD ∪ drop0) drop1)
  have hpair := Finset.card_union_le dropD drop0
  have hsplit : retained.card + (seeds.filter (fun g => ¬ keep g)).card = seeds.card :=
    Finset.card_filter_add_card_filter_not _
  refine ⟨retained, Finset.filter_subset _ _, by omega, ?_⟩
  intro g hg
  obtain ⟨hD, h0, h1⟩ := (Finset.mem_filter.mp hg).2
  exact ⟨natDegree_eq_of_le_of_coeff_ne_zero (specializeAffine_natDegree_le A g) hD, h0, h1⟩

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
