import ProximityPrize.SubmissionLower.Koala6844SeedChart


namespace ProximityPrize.SubmissionLower.Koala6844SeedChart

open Polynomial Koala6844Normalization
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {K I : Type} [Field K] [DecidableEq K] [DecidableEq I]

private theorem coprime_const_mul {d A : K[X]} {c : K}
    (hc : c ≠ 0) (h : IsCoprime A d) :
    IsCoprime (C c * A) d := by
  obtain ⟨u, v, heq⟩ := h
  refine ⟨C c⁻¹ * u, v, ?_⟩
  calc
    C c⁻¹ * u * (C c * A) + v * d = (C c⁻¹ * C c) * (u * A) + v * d := by ring
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one, one_mul, heq]

private theorem coprime_shear {A : Fin 2 → K[X]} (ℓ : K)
    (h : IsCoprime (A 0) (A 1)) :
    IsCoprime (shear A ℓ 0) (shear A ℓ 1) := by
  obtain ⟨u, v, heq⟩ := h
  refine ⟨u - v * C ℓ, v, ?_⟩
  rw [shear_zero, shear_one]
  linear_combination heq

theorem transport_chart {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
    {w agreement errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w agreement errors excess) (ℓ : K) :
    ∃ shifted : CenteredVirtualData x nodes σ w agreement errors excess,
      data.seeds.card ≤ shifted.seeds.card + 1 ∧ shifted.d0 = data.d0 ∧
      shifted.A0 = shear data.A0 ℓ := by
  let original := data.seeds.filter fun g => 1 - ℓ * g ≠ 0
  let seeds := original.image (forward ℓ)
  have hpre (t : K) (ht : t ∈ seeds) :
      backward ℓ t ∈ data.seeds ∧ scale ℓ t ≠ 0 ∧ forward ℓ (backward ℓ t) = t := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hseed, hunit⟩ := Finset.mem_filter.mp hg
    exact ⟨(backward_forward ℓ g hunit).symm ▸ hseed,
      scale_forward_ne_zero ℓ g hunit, congrArg (forward ℓ) (backward_forward ℓ g hunit)⟩
  have hzero : 0 ∈ seeds := by
    refine Finset.mem_image.mpr ⟨0, Finset.mem_filter.mpr ⟨data.zero_mem, by simp⟩, ?_⟩
    simp [forward]
  let selected (t : K) := C (scale ℓ t) * data.selected (backward ℓ t)
  let normalized (t : K) := data.normalized (backward ℓ t)
  let received (j : Fin 2) (i : I) :=
    if j = 0 then data.received 0 i else data.received 1 i + ℓ * data.received 0 i
  have hreceived₀ (i : I) : received 0 i = data.received 0 i := by simp [received]
  have hreceived₁ (i : I) : received 1 i = data.received 1 i + ℓ * data.received 0 i := by
    simp [received]
  have hC (t : K) (ht : t ∈ seeds) :
      C (scale ℓ t) * C (backward ℓ t) = (C t : K[X]) := by
    rw [← map_mul, scale_mul_backward ℓ t (hpre t ht).2.1]
  have hden (t : K) (ht : t ∈ seeds) :
      specializeAffine (shear data.A0 ℓ) t =
        C (scale ℓ t) * specializeAffine data.A0 (backward ℓ t) :=
    specialize_shear data.A0 ℓ t (hpre t ht).2.1
  let shifted : CenteredVirtualData x nodes σ w agreement errors excess :=
    { data with
      seeds := seeds
      zero_mem := hzero
      selected := selected
      normalized := normalized
      received := received
      A0 := shear data.A0 ℓ
      coprime_A0 := coprime_shear ℓ data.coprime_A0
      support_le := by simpa only [affineDegree_shear] using data.support_le
      selected_degree := by
        intro t ht
        exact (Polynomial.natDegree_C_mul_le _ _).trans (data.selected_degree _ (hpre t ht).1)
      normalized_degree := by
        intro t ht
        rw [affineDegree_shear]
        exact data.normalized_degree _ (hpre t ht).1
      denominator_degree := by
        intro t ht
        rw [hden t ht, Polynomial.natDegree_mul (C_ne_zero.mpr (hpre t ht).2.1)
          (data.denominator_ne _ (hpre t ht).1), Polynomial.natDegree_C, Nat.zero_add,
          data.denominator_degree _ (hpre t ht).1, affineDegree_shear]
      denominator_ne := by
        intro t ht
        rw [hden t ht]
        exact mul_ne_zero (C_ne_zero.mpr (hpre t ht).2.1) (data.denominator_ne _ (hpre t ht).1)
      denominator_on_domain := by
        intro t ht i hi
        rw [hden t ht, Polynomial.eval_mul, Polynomial.eval_C]
        exact mul_ne_zero (hpre t ht).2.1 (data.denominator_on_domain _ (hpre t ht).1 i hi)
      coprime_denominator0 := by
        intro t ht
        rw [hden t ht]
        exact coprime_const_mul (hpre t ht).2.1 (data.coprime_denominator0 _ (hpre t ht).1)
      coprime_denominator1 := by
        intro t ht
        rw [hden t ht, Polynomial.map_mul, Polynomial.map_C]
        exact coprime_const_mul ((_root_.map_ne_zero σ.toRingHom).2 (hpre t ht).2.1)
          (data.coprime_denominator1 _ (hpre t ht).1)
      equation0 := by
        intro t ht
        have heq := data.equation0 _ (hpre t ht).1
        rw [hden t ht]
        dsimp only [normalized, selected]
        linear_combination C (scale ℓ t) * heq + hC t ht * data.C1
      equation1 := by
        intro t ht
        have heq := data.equation1 _ (hpre t ht).1
        have hc := congrArg (Polynomial.map σ.toRingHom) (hC t ht)
        simp only [Polynomial.map_mul, Polynomial.map_C] at hc
        rw [hden t ht, Polynomial.map_mul, Polynomial.map_C]
        dsimp only [normalized, selected]
        rw [Polynomial.map_mul, Polynomial.map_C]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at heq hc ⊢
        linear_combination C (σ (scale ℓ t)) * heq + hc * data.D1
      homogeneous := fun t ht => data.homogeneous _ (hpre t ht).1
      received_equation := by
        intro i hi j
        by_cases hj : j = 0
        · subst j
          simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, shear_zero, hreceived₀]
            using data.received_equation i hi 0
        · have hv : j.val ≠ 0 := fun hz => hj (Fin.ext hz)
          have hj' : j = 1 := Fin.ext (by omega)
          subst j
          have h₀ := data.received_equation i hi 0
          have h₁ := data.received_equation i hi 1
          simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] at h₀
          simp only [Fin.val_one, Nat.cast_one, one_mul] at h₁
          simp only [Fin.val_one, Nat.cast_one, one_mul, shear_one, eval_add, eval_mul, eval_C,
            hreceived₁]
          linear_combination h₁ + ℓ * h₀
      agreements := by
        intro t ht
        refine (data.agreements _ (hpre t ht).1).trans (Finset.card_le_card ?_)
        intro i hi
        obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨hi, ?_⟩
        change (C (scale ℓ t) * data.selected (backward ℓ t)).eval (x i) =
          received 0 i + t * received 1 i
        rw [eval_mul, eval_C, heq, hreceived₀, hreceived₁, mul_add, ← mul_assoc,
          scale_mul_backward ℓ t (hpre t ht).2.1]
        unfold scale
        ring
      normalized_agreements := fun t ht => data.normalized_agreements _ (hpre t ht).1
      pencil := by
        intro P₀ P₁ hP₀ hP₁
        let D := P₁ - C ℓ * P₀
        have hD : D.natDegree ≤ w :=
          (natDegree_sub_le _ _).trans (max_le hP₁ ((natDegree_C_mul_le _ _).trans hP₀))
        let hits := data.seeds.filter fun g => data.selected g = P₀ + C g * D
        have hcover : (seeds.filter fun t => selected t = P₀ + C t * P₁) ⊆
            hits.image (forward ℓ) := by
          intro t ht
          obtain ⟨ht, hP⟩ := Finset.mem_filter.mp ht
          obtain ⟨hmem, hscale, hforward⟩ := hpre t ht
          refine Finset.mem_image.mpr ⟨backward ℓ t, Finset.mem_filter.mpr ⟨hmem, ?_⟩, hforward⟩
          apply mul_left_cancel₀ (C_ne_zero.mpr hscale)
          change selected t = C (scale ℓ t) * (P₀ + C (backward ℓ t) * D)
          rw [hP, mul_add, ← mul_assoc, hC t ht]
          dsimp only [scale, D]
          rw [map_add, map_one, map_mul]
          ring
        exact (Finset.card_le_card hcover).trans
          (Finset.card_image_le.trans (data.pencil P₀ D hP₀ hD)) }
  exact ⟨shifted, card_le_chart_add_one ℓ data.seeds, rfl, rfl⟩

theorem exists_admissible_chart [Fintype K]
    {x : I ↪ K} {nodes : Finset I} {σ : K ≃+* K}
    {w agreement errors excess : ℕ}
    (data : CenteredVirtualData x nodes σ w agreement errors excess)
    (hsize : nodes.card < Fintype.card K) :
    ∃ shifted : CenteredVirtualData x nodes σ w agreement errors excess,
      data.seeds.card ≤ shifted.seeds.card + 1 ∧
      shifted.d0.natDegree + affineDegree shifted.A0 =
        data.d0.natDegree + affineDegree data.A0 ∧
      ∀ i ∈ nodes, (shifted.A0 1).eval (x i) ≠ 0 := by
  have hconstant (i : I) (hi : i ∈ nodes) : (data.A0 0).eval (x i) ≠ 0 := by
    simpa only [specializeAffine, map_zero, zero_mul, add_zero]
      using data.denominator_on_domain 0 data.zero_mem i hi
  obtain ⟨ℓ, hℓ⟩ := exist_admissible_shear x nodes data.A0 hconstant hsize
  obtain ⟨shifted, hcard, hd, hA⟩ := transport_chart data ℓ
  refine ⟨shifted, hcard, ?_, ?_⟩
  · rw [hd, hA, affineDegree_shear]
  · rw [hA]
    exact hℓ

end

end ProximityPrize.SubmissionLower.Koala6844SeedChart

