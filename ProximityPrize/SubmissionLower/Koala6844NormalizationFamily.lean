import ProximityPrize.SubmissionLower.Koala6844NormalizationInfinity


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

noncomputable section

variable {K I : Type*} [Field K] [DecidableEq K] [DecidableEq I]

theorem card_centered_seeds (seeds : Finset K) (g0 : K) :
    (seeds.image fun g => g - g0).card = seeds.card :=
  Finset.card_image_of_injective _ (sub_left_injective)

theorem mem_centered_seeds {seeds : Finset K} {g0 g : K} :
    g ∈ seeds.image (fun h => h - g0) ↔ g0 + g ∈ seeds := by
  constructor
  · intro h
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp h
    simpa [add_comm, sub_add_cancel] using hOld
  · intro h
    refine Finset.mem_image.mpr ⟨g0 + g, h, ?_⟩
    ring

theorem centered_pencil_cap (seeds : Finset K) (selected : K → Polynomial K) (g0 : K)
    (w e : ℕ) (hP0 : (selected g0).natDegree ≤ w)
    (hPencil : ∀ P0 P1 : Polynomial K, P0.natDegree ≤ w → P1.natDegree ≤ w →
      (seeds.filter fun g => selected g = P0 + C g * P1).card ≤ e + 1) :
    ∀ P0 P1 : Polynomial K, P0.natDegree ≤ w → P1.natDegree ≤ w →
      ((seeds.image fun g => g - g0).filter fun g =>
        selected (g0 + g) - selected g0 = P0 + C g * P1).card ≤ e + 1 := by
  intro P0 P1 h0 h1
  let oldP0 := P0 + selected g0 - C g0 * P1
  have hOldP0 : oldP0.natDegree ≤ w :=
    (natDegree_sub_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le h0 hP0))
      ((natDegree_C_mul_le _ _).trans h1))
  let filtered := (seeds.image fun g => g - g0).filter fun g =>
    selected (g0 + g) - selected g0 = P0 + C g * P1
  have himage : (filtered.image fun g => g0 + g) ⊆
      seeds.filter fun g => selected g = oldP0 + C g * P1 := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    have ⟨hseed, hEq⟩ := Finset.mem_filter.mp hh
    refine Finset.mem_filter.mpr ⟨mem_centered_seeds.mp hseed, ?_⟩
    simp only [oldP0, map_add]
    linear_combination hEq
  rw [← Finset.card_image_of_injective filtered (add_right_injective g0)]
  exact (Finset.card_le_card himage).trans (hPencil oldP0 P1 hOldP0 h1)

theorem centered_agreement_cap (x : I ↪ K) (nodes : Finset I)
    (received : Fin 2 → I → K) (selected : K → Polynomial K) (g0 g : K) (A : ℕ)
    (h : A ≤ (nodes.filter fun i =>
      (selected (g0 + g)).eval (x i) = received 0 i + (g0 + g) * received 1 i).card) :
    A ≤ (nodes.filter fun i =>
      (selected (g0 + g) - selected g0).eval (x i) =
        centerReceived received x g0 (selected g0) 0 i +
          g * centerReceived received x g0 (selected g0) 1 i).card := by
  refine h.trans (Finset.card_le_card ?_)
  intro i hi
  have ⟨hnode, hfit⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hnode, center_agrees_at received x i g0 g _ _ hfit⟩

theorem centered_normalized_agreement_cap (x : I ↪ K) (nodes : Finset I)
    (fixed : I → K) (Q0 Q : Polynomial K) (A : ℕ)
    (h : A ≤ (nodes.filter fun i => Q.eval (x i) = fixed i).card) :
    A ≤ (nodes.filter fun i => (Q - Q0).eval (x i) = fixed i - Q0.eval (x i)).card := by
  simpa only [eval_sub, sub_left_inj] using h

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
