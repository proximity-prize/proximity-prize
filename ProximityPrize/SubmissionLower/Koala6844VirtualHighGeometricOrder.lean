import ProximityPrize.SubmissionLower.Koala6844VirtualHighRawLocal


namespace ProximityPrize.SubmissionLower.Koala6844VirtualHigh

open Koala6831Intrinsic RCN072 RCN135 RCN136 RCN219 RCN218 RCN264

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

theorem geometric_primary_of_original_primary
    (F N : Carrier K) (G : MvPolynomial (Fin 3) (GenericField K))
    (C : Ideal (MvPolynomial (Fin 3) (GenericField K)))
    (hdiv : G ∣ surfaceMap (polynomialEmbedding K) F) (μ : ℕ)
    (primary : ∃ s : Carrier K, s ∉ originalPrime C ∧
      s * N ∈ factorIdeal F ⊔ (originalPrime C)^μ) :
    ∃ s ∉ C, s * surfaceMap (polynomialEmbedding K) N ∈ Ideal.span {G} ⊔ C^μ := by
  let f := surfaceMap (polynomialEmbedding K)
  obtain ⟨s, hs, hmul⟩ := primary
  have hmapF : Ideal.map f (factorIdeal F) ≤ Ideal.span {G} := by
    rw [factorIdeal, Ideal.map_span, Set.image_singleton]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_span_singleton.mpr hdiv))
  have hmapC : Ideal.map f (originalPrime C) ≤ C := Ideal.map_le_iff_le_comap.mpr le_rfl
  have hmapPow : Ideal.map f ((originalPrime C)^μ) ≤ C^μ := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmapC _
  refine ⟨f s, fun hm => hs ((mem_originalPrime_iff C s).2 hm), ?_⟩
  have hmapped : f (s*N) ∈ Ideal.map f (factorIdeal F ⊔ (originalPrime C)^μ) :=
    Ideal.mem_map_of_mem f hmul
  rw [Ideal.map_sup, map_mul] at hmapped
  exact (sup_le_sup hmapF hmapPow) hmapped

theorem geometric_order_rawTrimmedTail (F V W : Carrier K) (first p : ℕ) [CharP K p]
    (hp : p.Prime) (G : MvPolynomial (Fin 3) (GenericField K))
    (hG : G ∣ surfaceMap (polynomialEmbedding K) F) (hF : Irreducible F)
    (proper : ¬ F ∣ rawTrimmedTail F V W first)
    (C : RegularComponent (GenericField K) G
      (surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W first))
      (surfaceMap (polynomialEmbedding K) (V * implicitRegularity F))) :
    ∃ μ : ℕ, 1 ≤ μ ∧
      (∃ s ∉ C.1, s * surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W first) ∈
        Ideal.span {G} ⊔ C.1^μ) ∧
      ((∃ delay, 1 ≤ delay ∧ delay ≤ μ ∧
        surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (first+delay)) ∉ C.1) ∨
        (∀ delay, surfaceMap (polynomialEmbedding K) (rawTrimmedTail F V W (first+delay)) ∈ C.1)) := by
  let f := surfaceMap (polynomialEmbedding K)
  have hheight : C.1.height ≤ 2 :=
    component_height_le_two _ _ _ _ (regularComponent_mem _ _ _ _ C)
  have hgmem := regularComponent_G_mem _ _ _ _ C
  have hFmem : f F ∈ C.1 := Ideal.mem_of_dvd C.1 hG hgmem
  have hTmem := regularComponent_T_mem _ _ _ _ C
  have hH : f V * f (implicitRegularity F) ∉ C.1 := by
    intro h
    exact regularComponent_H_not_mem _ _ _ _ C
      ((congrArg (fun t => t ∈ C.1) (map_mul f V (implicitRegularity F))).mpr h)
  have hV : f V ∉ C.1 := fun h => hH (Ideal.mul_mem_right _ _ h)
  have hS : f (implicitRegularity F) ∉ C.1 := fun h => hH (Ideal.mul_mem_left _ _ h)
  obtain ⟨μ, positive, primary, decision⟩ := localOrder_rawTrimmedTail
    F V W first p hp C.1 hheight hF hFmem hS hV hTmem proper
  exact ⟨μ, positive, geometric_primary_of_original_primary F _ G C.1 hG μ primary, decision⟩

end

end ProximityPrize.SubmissionLower.Koala6844VirtualHigh

