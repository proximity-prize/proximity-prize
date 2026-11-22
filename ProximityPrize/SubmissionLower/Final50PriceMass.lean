import ProximityPrize.SubmissionLower.Final50PriceCaps

set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Final50PriceMass
open Final50PriceCaps (Band start thresholds order)
open Final50Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (zeroShape)
open Final50PriceLayer (fastLayer availableMass)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.sumBelow_add
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, Final50PriceLayer.availableMass_eq_sum hr hj le_rfl]

private def blockBound (f : ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | o, l :: ls => l * f o + blockBound f (o + l) ls

private def blocksOk (L : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | o, l :: ls => (decide (o + l ≤ L) || decide (L ≤ o)) && blocksOk L (o + l) ls

private theorem block_le (f : ℕ → ℕ) (o l : ℕ) (h : ∀ t < l, f (o + t) ≤ f o) :
    P3_6_8_1.sumBelow (fun k => f (o + k)) l ≤ l * f o := by
  induction l with
  | zero => simp [P3_6_8_1.sumBelow]
  | succ n ih =>
    rw [P3_6_8_1.sumBelow, Nat.add_one_mul]
    exact Nat.add_le_add (ih fun t ht => h t (by omega)) (h n (by omega))

private theorem blocks_le (f : ℕ → ℕ) (L : ℕ)
    (H : ∀ i k, i ≤ k → (L ≤ i ∨ k < L) → f k ≤ f i) :
    ∀ (lens : List ℕ) (o : ℕ), blocksOk L o lens = true →
      P3_6_8_1.sumBelow (fun k => f (o + k)) lens.sum ≤ blockBound f o lens
  | [], _, _ => by simp [P3_6_8_1.sumBelow, blockBound]
  | l :: ls, o, h => by
    simp only [blocksOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    have e : P3_6_8_1.sumBelow (fun k => f (o + k)) (l + ls.sum) =
        P3_6_8_1.sumBelow (fun k => f (o + k)) l + P3_6_8_1.sumBelow (fun k => f (o + l + k)) ls.sum := by
      rw [P3_6_8_1.sumBelow_add]; simp only [Nat.add_assoc]
    rw [List.sum_cons, e, blockBound]
    have hb : ∀ t < l, f (o + t) ≤ f o := by
      intro t ht
      apply H o (o + t) (by omega)
      rcases h.1 with h1 | h1
      · exact Or.inr (by omega)
      · exact Or.inl h1
    exact Nat.add_le_add (block_le f o l hb) (blocks_le f L H ls (o + l) h.2)

private theorem fastLayer_anti (r y : Shape) (L : ℕ) :
    ∀ i k, i ≤ k → (L ≤ i ∨ k < L) → fastLayer r y L k ≤ fastLayer r y L i := by
  intro i k hik hs
  have hm : K1_13_8.fastRemaining ((k+1)*r.b + (k+1-L)*y.b) ((k+1)*r.j + (k+1-L)*y.j) ≤
      K1_13_8.fastRemaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j) := by
    have := K1_13_8.remaining_anti
      (Nat.add_le_add (Nat.mul_le_mul (show i+1 ≤ k+1 by omega) (le_refl r.b))
        (Nat.mul_le_mul (show i+1-L ≤ k+1-L by omega) (le_refl y.b)))
      (Nat.add_le_add (Nat.mul_le_mul (show i+1 ≤ k+1 by omega) (le_refl r.j))
        (Nat.mul_le_mul (show i+1-L ≤ k+1-L by omega) (le_refl y.j)))
    rwa [symbol_count, symbol_count] at this
  unfold fastLayer
  rcases hs with hs | hs
  · rw [if_neg (show ¬(r.j = 0 ∧ k < L) by omega), if_neg (show ¬(r.j = 0 ∧ i < L) by omega)]
    exact hm
  · by_cases hr : r.j = 0
    · rw [if_pos (show r.j = 0 ∧ k < L from ⟨hr, hs⟩), if_pos (show r.j = 0 ∧ i < L from ⟨hr, by omega⟩)]
    · rw [if_neg (show ¬(r.j = 0 ∧ k < L) by omega), if_neg (show ¬(r.j = 0 ∧ i < L) by omega)]
      exact hm

private theorem mass_of_blocks (r y : Shape) (L N : ℕ) (lens : List ℕ)
    (h : (decide (lens.sum = N) && blocksOk L 0 lens && decide (blockBound (fastLayer r y L) 0 lens < layerNeed)) = true) :
    P3_6_8_1.sumBelow (fastLayer r y L) N < layerNeed := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hN, hok⟩, hb⟩ := h
  have := blocks_le (fastLayer r y L) L (fastLayer_anti r y L) lens 0 hok
  simp only [Nat.zero_add] at this
  rw [← hN]
  exact this.trans_lt hb

private theorem m0_0 : availableMass (start .empty) ⟨3,9,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨3,9,0⟩ 5 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨3,9,0⟩ 5 188 [5,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,5,5,5,6,6,6,7,8,10,13,22] (by decide +kernel)

private theorem m0_1 : availableMass (start .empty) ⟨4,12,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .empty) ⟨4,12,0⟩ 13 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨4,12,0⟩ 13 150 [13,7,7,8,8,9,10,11,12,14,19,32] (by decide +kernel)

private theorem m0_2 : availableMass (start .empty) ⟨5,8,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,8,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨5,8,0⟩ 1 207 [1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,5,5,5,5,6,6,7,8,10,13,22] (by decide +kernel)

private theorem m0_3 : availableMass (start .empty) ⟨5,15,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .empty) ⟨5,15,0⟩ 22 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨5,15,0⟩ 22 132 [22,5,5,5,5,6,6,6,7,8,9,10,14,24] (by decide +kernel)

private theorem m0_4 : availableMass (start .empty) ⟨7,21,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨7,21,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨7,21,0⟩ 23 101 [23,12,15,19,32] (by decide +kernel)

private theorem m0_5 : availableMass (start .empty) ⟨8,23,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .empty) ⟨8,23,0⟩ 24 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨8,23,0⟩ 24 95 [24,11,13,17,30] (by decide +kernel)

private theorem m0_6 : availableMass (start .empty) ⟨9,26,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .empty) ⟨9,26,0⟩ 25 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨9,26,0⟩ 25 88 [25,14,18,31] (by decide +kernel)

private theorem m0_7 : availableMass (start .empty) ⟨10,30,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨10,30,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨10,30,0⟩ 39 94 [39,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,3,4,7] (by decide +kernel)

private theorem m0_8 : availableMass (start .empty) ⟨12,7,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨12,7,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨12,7,0⟩ 1 236 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,4,4,4,4,5,5,5,6,7,9,11,20] (by decide +kernel)

private theorem m0_9 : availableMass (start .empty) ⟨12,36,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨12,36,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨12,36,0⟩ 40 85 [40,3,3,3,3,3,4,4,5,6,11] (by decide +kernel)

private theorem m0_10 : availableMass (start .empty) ⟨13,39,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨13,39,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨13,39,0⟩ 42 84 [42,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,3,3,4,8] (by decide +kernel)

private theorem m0_11 : availableMass (start .empty) ⟨15,45,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨15,45,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨15,45,0⟩ 43 79 [43,2,2,2,2,2,2,2,3,3,3,5,8] (by decide +kernel)

private theorem m0_12 : availableMass (start .empty) ⟨18,7,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,7,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨18,7,0⟩ 2 237 [2,6,6,7,7,7,8,8,9,9,10,11,12,14,17,22,34,48] (by decide +kernel)

private theorem m0_13 : availableMass (start .empty) ⟨18,10,0⟩ 8 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,10,0⟩ 8 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨18,10,0⟩ 8 173 [8,12,14,16,19,23,33,48] (by decide +kernel)

private theorem m0_14 : availableMass (start .empty) ⟨18,52,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨18,52,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨18,52,0⟩ 45 76 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4] (by decide +kernel)

private theorem m0_15 : availableMass (start .empty) ⟨19,6,0⟩ 2 < layerNeed := by
  rw [mass_eq (start .empty) ⟨19,6,0⟩ 2 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨19,6,0⟩ 2 277 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,5,5,5,6,6,7,8,9,10,14,29,48] (by decide +kernel)

private theorem m0_16 : availableMass (start .empty) ⟨20,9,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .empty) ⟨20,9,0⟩ 15 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨20,9,0⟩ 15 198 [15,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,4,4,5,5,6,8,10,20] (by decide +kernel)

private theorem m0_17 : availableMass (start .empty) ⟨23,51,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨23,51,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨23,51,0⟩ 44 76 [44,2,2,2,2,3,3,4,5,9] (by decide +kernel)

private theorem m0_18 : availableMass (start .empty) ⟨24,24,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .empty) ⟨24,24,0⟩ 33 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨24,24,0⟩ 33 101 [33,5,6,7,8,9,12,21] (by decide +kernel)

private theorem m0_19 : availableMass (start .empty) ⟨25,27,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨25,27,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨25,27,0⟩ 35 96 [35,5,5,6,7,8,11,19] (by decide +kernel)

private theorem m0_20 : availableMass (start .empty) ⟨27,6,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .empty) ⟨27,6,0⟩ 5 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨27,6,0⟩ 5 280 [5,8,9,9,10,11,12,14,16,18,24,48,48,48] (by decide +kernel)

private theorem m0_21 : availableMass (start .empty) ⟨30,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .empty) ⟨30,3,0⟩ 1 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨30,3,0⟩ 1 551 [1,8,9,9,9,10,10,11,12,12,13,16,47,48,48,48,48,48,48,48,48] (by decide +kernel)

private theorem m0_22 : availableMass (start .empty) ⟨34,3,0⟩ 4 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,3,0⟩ 4 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨34,3,0⟩ 4 554 [4,11,12,13,13,14,15,17,23,48,48,48,48,48,48,48,48,48] (by decide +kernel)

private theorem m0_23 : availableMass (start .empty) ⟨34,17,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .empty) ⟨34,17,0⟩ 29 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨34,17,0⟩ 29 126 [29,5,6,6,7,8,9,11,15,30] (by decide +kernel)

private theorem m0_24 : availableMass (start .empty) ⟨35,6,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .empty) ⟨35,6,0⟩ 16 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨35,6,0⟩ 16 291 [16,3,3,3,3,3,4,4,4,4,4,4,4,5,5,5,5,5,6,6,7,8,9,27,48,48,48] (by decide +kernel)

private theorem m0_25 : availableMass (start .empty) ⟨35,19,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .empty) ⟨35,19,0⟩ 31 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨35,19,0⟩ 31 117 [31,5,5,5,6,7,8,10,14,26] (by decide +kernel)

private theorem m0_26 : availableMass (start .empty) ⟨36,9,0⟩ 22 < layerNeed := by
  rw [mass_eq (start .empty) ⟨36,9,0⟩ 22 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨36,9,0⟩ 22 205 [22,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,5,5,5,6,7,8,10,32,48] (by decide +kernel)

private theorem m0_27 : availableMass (start .empty) ⟨36,21,0⟩ 34 < layerNeed := by
  rw [mass_eq (start .empty) ⟨36,21,0⟩ 34 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨36,21,0⟩ 34 112 [34,3,3,3,3,4,4,4,5,5,6,8,11,19] (by decide +kernel)

private theorem m0_28 : availableMass (start .empty) ⟨37,12,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,12,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨37,12,0⟩ 23 160 [23,7,7,8,9,10,12,15,21,48] (by decide +kernel)

private theorem m0_29 : availableMass (start .empty) ⟨37,15,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,15,0⟩ 27 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨37,15,0⟩ 27 137 [27,6,6,7,7,8,10,12,18,36] (by decide +kernel)

private theorem m0_30 : availableMass (start .empty) ⟨37,23,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,23,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨37,23,0⟩ 35 106 [35,3,4,4,4,5,6,6,8,11,20] (by decide +kernel)

private theorem m0_31 : availableMass (start .empty) ⟨37,26,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨37,26,0⟩ 36 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨37,26,0⟩ 36 99 [36,4,4,5,6,6,8,11,19] (by decide +kernel)

private theorem m0_32 : availableMass (start .empty) ⟨38,28,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨38,28,0⟩ 37 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨38,28,0⟩ 37 95 [37,4,4,5,5,6,7,10,17] (by decide +kernel)

private theorem m0_33 : availableMass (start .empty) ⟨40,31,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨40,31,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨40,31,0⟩ 40 93 [40,2,2,2,2,2,2,2,3,3,3,3,4,5,6,12] (by decide +kernel)

private theorem m0_34 : availableMass (start .empty) ⟨41,30,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨41,30,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨41,30,0⟩ 40 95 [40,1,1,1,1,2,2,2,2,2,2,2,2,2,2,3,3,4,4,6,11] (by decide +kernel)

private theorem m0_35 : availableMass (start .empty) ⟨42,33,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨42,33,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨42,33,0⟩ 41 91 [41,1,1,1,2,2,2,2,2,2,2,2,2,3,3,3,4,6,10] (by decide +kernel)

private theorem m0_36 : availableMass (start .empty) ⟨42,48,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨42,48,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨42,48,0⟩ 44 78 [44,2,2,2,2,2,3,3,4,5,9] (by decide +kernel)

private theorem m0_37 : availableMass (start .empty) ⟨42,51,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨42,51,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨42,51,0⟩ 45 77 [45,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,7] (by decide +kernel)

private theorem m0_38 : availableMass (start .empty) ⟨49,50,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨49,50,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨49,50,0⟩ 45 78 [45,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,7] (by decide +kernel)

private theorem m0_39 : availableMass (start .empty) ⟨51,3,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .empty) ⟨51,3,0⟩ 15 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨51,3,0⟩ 15 565 [15,15,17,18,20,48,48,48,48,48,48,48,48,48,48] (by decide +kernel)

private theorem m0_40 : availableMass (start .empty) ⟨56,47,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨56,47,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨56,47,0⟩ 44 79 [44,2,2,2,2,2,3,3,4,5,10] (by decide +kernel)

private theorem m0_41 : availableMass (start .empty) ⟨56,48,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨56,48,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨56,48,0⟩ 45 79 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,3,6] (by decide +kernel)

private theorem m0_42 : availableMass (start .empty) ⟨57,43,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨57,43,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨57,43,0⟩ 44 82 [44,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,3,4,8] (by decide +kernel)

private theorem m0_43 : availableMass (start .empty) ⟨64,42,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨64,42,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨64,42,0⟩ 44 83 [44,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,3,5,8] (by decide +kernel)

private theorem m0_44 : availableMass (start .empty) ⟨67,3,0⟩ 18 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,3,0⟩ 18 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨67,3,0⟩ 18 568 [18,20,23,27,48,48,48,48,48,48,48,48,48,48] (by decide +kernel)

private theorem m0_45 : availableMass (start .empty) ⟨67,17,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .empty) ⟨67,17,0⟩ 35 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨67,17,0⟩ 35 132 [35,4,4,4,5,5,6,7,8,11,43] (by decide +kernel)

private theorem m0_46 : availableMass (start .empty) ⟨68,6,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,6,0⟩ 20 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨68,6,0⟩ 20 295 [20,14,16,18,35,48,48,48,48] (by decide +kernel)

private theorem m0_47 : availableMass (start .empty) ⟨68,9,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,9,0⟩ 23 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨68,9,0⟩ 23 206 [23,13,15,20,39,48,48] (by decide +kernel)

private theorem m0_48 : availableMass (start .empty) ⟨68,19,0⟩ 36 < layerNeed := by
  rw [mass_eq (start .empty) ⟨68,19,0⟩ 36 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨68,19,0⟩ 36 122 [36,3,4,4,4,5,6,7,8,12,33] (by decide +kernel)

private theorem m0_49 : availableMass (start .empty) ⟨69,12,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,12,0⟩ 25 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨69,12,0⟩ 25 162 [25,12,15,20,42,48] (by decide +kernel)

private theorem m0_50 : availableMass (start .empty) ⟨69,15,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,15,0⟩ 29 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨69,15,0⟩ 29 139 [29,10,12,15,25,48] (by decide +kernel)

private theorem m0_51 : availableMass (start .empty) ⟨69,41,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨69,41,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨69,41,0⟩ 44 84 [44,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,5,8] (by decide +kernel)

private theorem m0_52 : availableMass (start .empty) ⟨70,39,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨70,39,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨70,39,0⟩ 43 85 [43,2,2,2,2,2,3,3,4,4,6,12] (by decide +kernel)

private theorem m0_53 : availableMass (start .empty) ⟨71,32,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,32,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨71,32,0⟩ 41 92 [41,2,3,3,3,3,4,4,6,8,15] (by decide +kernel)

private theorem m0_54 : availableMass (start .empty) ⟨71,35,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,35,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨71,35,0⟩ 43 90 [43,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,5,9] (by decide +kernel)

private theorem m0_55 : availableMass (start .empty) ⟨71,46,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨71,46,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨71,46,0⟩ 45 80 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,3,6] (by decide +kernel)

private theorem m0_56 : availableMass (start .empty) ⟨77,45,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨77,45,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨77,45,0⟩ 45 81 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,3,6] (by decide +kernel)

private theorem m0_57 : availableMass (start .empty) ⟨79,53,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨79,53,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨79,53,0⟩ 46 77 [46,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,3,6] (by decide +kernel)

private theorem m0_58 : availableMass (start .empty) ⟨80,52,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨80,52,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨80,52,0⟩ 46 77 [46,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4] (by decide +kernel)

private theorem m0_59 : availableMass (start .empty) ⟨82,44,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨82,44,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨82,44,0⟩ 45 82 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,6] (by decide +kernel)

private theorem m0_60 : availableMass (start .empty) ⟨85,23,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .empty) ⟨85,23,0⟩ 37 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨85,23,0⟩ 37 108 [37,5,6,7,9,13,31] (by decide +kernel)

private theorem m0_61 : availableMass (start .empty) ⟨85,26,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨85,26,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨85,26,0⟩ 39 102 [39,4,4,5,6,8,11,25] (by decide +kernel)

private theorem m0_62 : availableMass (start .empty) ⟨86,28,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨86,28,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨86,28,0⟩ 40 98 [40,3,4,4,4,5,7,10,21] (by decide +kernel)

private theorem m0_63 : availableMass (start .empty) ⟨86,37,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨86,37,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨86,37,0⟩ 44 88 [44,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,6] (by decide +kernel)

private theorem m0_64 : availableMass (start .empty) ⟨87,51,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨87,51,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨87,51,0⟩ 46 78 [46,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4] (by decide +kernel)

private theorem m0_65 : availableMass (start .empty) ⟨94,42,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨94,42,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨94,42,0⟩ 45 84 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,5] (by decide +kernel)

private theorem m0_66 : availableMass (start .empty) ⟨94,50,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨94,50,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨94,50,0⟩ 46 79 [46,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,5] (by decide +kernel)

private theorem m0_67 : availableMass (start .empty) ⟨100,17,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .empty) ⟨100,17,0⟩ 38 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨100,17,0⟩ 38 135 [38,4,4,5,6,7,8,15,48] (by decide +kernel)

private theorem m0_68 : availableMass (start .empty) ⟨100,49,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨100,49,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨100,49,0⟩ 46 79 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m0_69 : availableMass (start .empty) ⟨101,15,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,15,0⟩ 31 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨101,15,0⟩ 31 141 [31,13,17,32,48] (by decide +kernel)

private theorem m0_70 : availableMass (start .empty) ⟨101,19,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,19,0⟩ 39 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨101,19,0⟩ 39 125 [39,4,4,4,5,5,7,9,48] (by decide +kernel)

private theorem m0_71 : availableMass (start .empty) ⟨101,26,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,26,0⟩ 42 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨101,26,0⟩ 42 105 [42,1,2,2,2,2,2,2,2,2,3,3,3,4,6,27] (by decide +kernel)

private theorem m0_72 : availableMass (start .empty) ⟨101,34,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,34,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨101,34,0⟩ 44 92 [44,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,11] (by decide +kernel)

private theorem m0_73 : availableMass (start .empty) ⟨101,41,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨101,41,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨101,41,0⟩ 45 85 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,7] (by decide +kernel)

private theorem m0_74 : availableMass (start .empty) ⟨102,28,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .empty) ⟨102,28,0⟩ 43 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨102,28,0⟩ 43 101 [43,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,21] (by decide +kernel)

private theorem m0_75 : availableMass (start .empty) ⟨106,48,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨106,48,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨106,48,0⟩ 46 80 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m0_76 : availableMass (start .empty) ⟨107,40,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨107,40,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨107,40,0⟩ 45 86 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,4,9] (by decide +kernel)

private theorem m0_77 : availableMass (start .empty) ⟨110,39,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨110,39,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨110,39,0⟩ 45 87 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,9] (by decide +kernel)

private theorem m0_78 : availableMass (start .empty) ⟨112,47,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨112,47,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨112,47,0⟩ 46 81 [46,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,5] (by decide +kernel)

private theorem m0_79 : availableMass (start .empty) ⟨117,21,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .empty) ⟨117,21,0⟩ 40 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨117,21,0⟩ 40 118 [40,4,5,5,7,9,48] (by decide +kernel)

private theorem m0_80 : availableMass (start .empty) ⟨117,23,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .empty) ⟨117,23,0⟩ 41 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨117,23,0⟩ 41 112 [41,3,4,4,5,6,8,41] (by decide +kernel)

private theorem m0_81 : availableMass (start .empty) ⟨117,46,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨117,46,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨117,46,0⟩ 46 81 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m0_82 : availableMass (start .empty) ⟨118,33,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .empty) ⟨118,33,0⟩ 44 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨118,33,0⟩ 44 94 [44,1,1,1,1,2,2,2,2,2,2,3,3,4,5,19] (by decide +kernel)

private theorem m0_83 : availableMass (start .empty) ⟨122,45,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨122,45,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨122,45,0⟩ 46 82 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m0_84 : availableMass (start .empty) ⟨126,36,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .empty) ⟨126,36,0⟩ 45 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨126,36,0⟩ 45 90 [45,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,4,16] (by decide +kernel)

private theorem m0_85 : availableMass (start .empty) ⟨127,44,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨127,44,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨127,44,0⟩ 46 83 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m0_86 : availableMass (start .empty) ⟨129,55,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .empty) ⟨129,55,0⟩ 47 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨129,55,0⟩ 47 77 [47,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,5] (by decide +kernel)

private theorem m0_87 : availableMass (start .empty) ⟨132,43,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .empty) ⟨132,43,0⟩ 46 (Or.inl rfl) (by decide)]
  exact mass_of_blocks (start .empty) ⟨132,43,0⟩ 46 84 [46,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,10] (by decide +kernel)

private theorem m1_0 : availableMass (start .one3) ⟨2,6,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one3) ⟨2,6,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨2,6,0⟩ 7 190 [7,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,5,5,5,5,5,6,6,7,7,8,9,11,15,26] (by decide +kernel)

private theorem m1_1 : availableMass (start .one3) ⟨3,9,0⟩ 12 < layerNeed := by
  rw [mass_eq (start .one3) ⟨3,9,0⟩ 12 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨3,9,0⟩ 12 149 [12,13,15,17,20,26,46] (by decide +kernel)

private theorem m1_2 : availableMass (start .one3) ⟨4,12,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .one3) ⟨4,12,0⟩ 27 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨4,12,0⟩ 27 137 [13,14,7,7,8,8,9,10,13,17,31] (by decide +kernel)

private theorem m1_3 : availableMass (start .one3) ⟨6,18,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one3) ⟨6,18,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨6,18,0⟩ 43 121 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,11] (by decide +kernel)

private theorem m1_4 : availableMass (start .one3) ⟨10,30,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3) ⟨10,30,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨10,30,0⟩ 47 97 [9,9,9,10,10,3,4,4,4,5,6,8,16] (by decide +kernel)

private theorem m1_5 : availableMass (start .one3) ⟨12,36,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨12,36,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨12,36,0⟩ 52 94 [2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,9] (by decide +kernel)

private theorem m1_6 : availableMass (start .one3) ⟨18,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one3) ⟨18,3,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨18,3,0⟩ 1 276 [1,3,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,6,6,6,6,7,7,8,9,9,11,12,15,20,37,48] (by decide +kernel)

private theorem m1_7 : availableMass (start .one3) ⟨19,6,0⟩ 14 < layerNeed := by
  rw [mass_eq (start .one3) ⟨19,6,0⟩ 14 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨19,6,0⟩ 14 197 [14,7,7,8,8,9,10,11,13,15,19,28,48] (by decide +kernel)

private theorem m1_8 : availableMass (start .one3) ⟨26,3,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one3) ⟨26,3,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨26,3,0⟩ 7 282 [7,8,9,9,10,11,12,14,15,19,24,48,48,48] (by decide +kernel)

private theorem m1_9 : availableMass (start .one3) ⟨34,3,0⟩ 10 < layerNeed := by
  rw [mass_eq (start .one3) ⟨34,3,0⟩ 10 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨34,3,0⟩ 10 285 [10,14,15,17,20,26,39,48,48,48] (by decide +kernel)

private theorem m1_10 : availableMass (start .one3) ⟨35,6,0⟩ 28 < layerNeed := by
  rw [mass_eq (start .one3) ⟨35,6,0⟩ 28 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨35,6,0⟩ 28 211 [7,7,7,7,3,3,3,3,4,4,4,4,4,4,5,5,5,6,6,7,8,10,13,34,48] (by decide +kernel)

private theorem m1_11 : availableMass (start .one3) ⟨51,3,0⟩ 14 < layerNeed := by
  rw [mass_eq (start .one3) ⟨51,3,0⟩ 14 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨51,3,0⟩ 14 289 [14,22,26,35,48,48,48,48] (by decide +kernel)

private theorem m1_12 : availableMass (start .one3) ⟨67,3,0⟩ 18 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,3,0⟩ 18 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨67,3,0⟩ 18 293 [18,20,25,38,48,48,48,48] (by decide +kernel)

private theorem m1_13 : availableMass (start .one3) ⟨67,6,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,6,0⟩ 42 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨67,6,0⟩ 42 225 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,4,32,48,48] (by decide +kernel)

private theorem m1_14 : availableMass (start .one3) ⟨67,28,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .one3) ⟨67,28,0⟩ 45 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨67,28,0⟩ 45 98 [15,15,15,5,6,8,11,23] (by decide +kernel)

private theorem m1_15 : availableMass (start .one3) ⟨68,43,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3) ⟨68,43,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨68,43,0⟩ 53 88 [6,6,6,7,7,7,7,7,2,2,2,2,3,3,4,6,11] (by decide +kernel)

private theorem m1_16 : availableMass (start .one3) ⟨69,34,0⟩ 48 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,34,0⟩ 48 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨69,34,0⟩ 48 92 [16,16,16,4,5,7,9,19] (by decide +kernel)

private theorem m1_17 : availableMass (start .one3) ⟨69,44,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨69,44,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨69,44,0⟩ 54 89 [4,5,5,5,5,5,5,5,5,5,5,1,1,1,1,2,2,2,2,2,3,3,5,10] (by decide +kernel)

private theorem m1_18 : availableMass (start .one3) ⟨70,24,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3) ⟨70,24,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨70,24,0⟩ 47 108 [11,12,12,12,3,4,4,5,5,7,10,23] (by decide +kernel)

private theorem m1_19 : availableMass (start .one3) ⟨70,39,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨70,39,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨70,39,0⟩ 54 93 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,9] (by decide +kernel)

private theorem m1_20 : availableMass (start .one3) ⟨71,30,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨71,30,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨71,30,0⟩ 52 102 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,4,5,13] (by decide +kernel)

private theorem m1_21 : availableMass (start .one3) ⟨84,3,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one3) ⟨84,3,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨84,3,0⟩ 21 296 [21,17,21,45,48,48,48,48] (by decide +kernel)

private theorem m1_22 : availableMass (start .one3) ⟨87,27,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨87,27,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨87,27,0⟩ 52 107 [2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,4,6,15] (by decide +kernel)

private theorem m1_23 : availableMass (start .one3) ⟨100,3,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,3,0⟩ 25 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨100,3,0⟩ 25 300 [25,16,19,48,48,48,48,48] (by decide +kernel)

private theorem m1_24 : availableMass (start .one3) ⟨100,9,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,9,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨100,9,0⟩ 47 184 [5,6,6,6,6,6,6,6,2,2,2,3,3,3,3,3,4,4,4,8,48,48] (by decide +kernel)

private theorem m1_25 : availableMass (start .one3) ⟨100,23,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,23,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨100,23,0⟩ 52 115 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,26] (by decide +kernel)

private theorem m1_26 : availableMass (start .one3) ⟨100,33,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,33,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨100,33,0⟩ 54 99 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,10] (by decide +kernel)

private theorem m1_27 : availableMass (start .one3) ⟨100,48,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨100,48,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨100,48,0⟩ 55 87 [4,4,4,4,4,5,5,5,5,5,5,5,1,1,1,1,1,2,2,2,2,2,3,4,10] (by decide +kernel)

private theorem m1_28 : availableMass (start .one3) ⟨101,29,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3) ⟨101,29,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨101,29,0⟩ 53 104 [2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,5,16] (by decide +kernel)

private theorem m1_29 : availableMass (start .one3) ⟨101,39,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨101,39,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨101,39,0⟩ 55 94 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,8] (by decide +kernel)

private theorem m1_30 : availableMass (start .one3) ⟨101,49,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨101,49,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨101,49,0⟩ 56 87 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,7] (by decide +kernel)

private theorem m1_31 : availableMass (start .one3) ⟨110,48,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨110,48,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨110,48,0⟩ 56 88 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,8] (by decide +kernel)

private theorem m1_32 : availableMass (start .one3) ⟨111,46,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨111,46,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨111,46,0⟩ 56 89 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,7] (by decide +kernel)

private theorem m1_33 : availableMass (start .one3) ⟨116,3,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .one3) ⟨116,3,0⟩ 29 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨116,3,0⟩ 29 304 [29,16,19,48,48,48,48,48] (by decide +kernel)

private theorem m1_34 : availableMass (start .one3) ⟨116,16,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3) ⟨116,16,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨116,16,0⟩ 51 137 [3,4,4,4,4,4,4,4,4,4,4,4,4,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,3,3,8,48] (by decide +kernel)

private theorem m1_35 : availableMass (start .one3) ⟨116,20,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3) ⟨116,20,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨116,20,0⟩ 52 123 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,4,39] (by decide +kernel)

private theorem m1_36 : availableMass (start .one3) ⟨117,32,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3) ⟨117,32,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨117,32,0⟩ 54 101 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,5,16] (by decide +kernel)

private theorem m1_37 : availableMass (start .one3) ⟨117,38,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3) ⟨117,38,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨117,38,0⟩ 55 95 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,11] (by decide +kernel)

private theorem m1_38 : availableMass (start .one3) ⟨117,45,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨117,45,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨117,45,0⟩ 56 90 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,7] (by decide +kernel)

private theorem m1_39 : availableMass (start .one3) ⟨125,44,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨125,44,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨125,44,0⟩ 56 91 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,8] (by decide +kernel)

private theorem m1_40 : availableMass (start .one3) ⟨129,43,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3) ⟨129,43,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3) ⟨129,43,0⟩ 56 91 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,8] (by decide +kernel)

private theorem m2_0 : availableMass (start .one3wide) ⟨2,6,0⟩ 8 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨2,6,0⟩ 8 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨2,6,0⟩ 8 191 [4,4,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,5,5,5,5,5,6,6,7,7,8,9,11,15,26] (by decide +kernel)

private theorem m2_1 : availableMass (start .one3wide) ⟨3,9,0⟩ 13 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨3,9,0⟩ 13 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨3,9,0⟩ 13 150 [13,13,15,17,20,26,46] (by decide +kernel)

private theorem m2_2 : availableMass (start .one3wide) ⟨4,12,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨4,12,0⟩ 29 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨4,12,0⟩ 29 139 [9,10,10,6,6,7,7,8,9,10,12,16,29] (by decide +kernel)

private theorem m2_3 : availableMass (start .one3wide) ⟨7,21,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨7,21,0⟩ 42 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨7,21,0⟩ 42 110 [10,10,11,11,4,4,5,5,6,6,8,10,20] (by decide +kernel)

private theorem m2_4 : availableMass (start .one3wide) ⟨10,28,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨10,28,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨10,28,0⟩ 44 97 [14,15,15,5,5,6,8,10,19] (by decide +kernel)

private theorem m2_5 : availableMass (start .one3wide) ⟨10,30,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨10,30,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨10,30,0⟩ 49 99 [6,6,6,6,6,6,6,7,2,2,2,2,3,3,3,4,4,5,7,13] (by decide +kernel)

private theorem m2_6 : availableMass (start .one3wide) ⟨13,39,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨13,39,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨13,39,0⟩ 50 89 [10,10,10,10,10,4,4,5,5,7,14] (by decide +kernel)

private theorem m2_7 : availableMass (start .one3wide) ⟨18,3,0⟩ 5 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨18,3,0⟩ 5 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨18,3,0⟩ 5 280 [2,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,5,5,5,6,7,8,9,12,37,48] (by decide +kernel)

private theorem m2_8 : availableMass (start .one3wide) ⟨19,6,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨19,6,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨19,6,0⟩ 15 198 [15,7,7,8,8,9,10,11,13,15,19,28,48] (by decide +kernel)

private theorem m2_9 : availableMass (start .one3wide) ⟨26,3,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨26,3,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨26,3,0⟩ 7 282 [7,11,11,12,14,15,18,21,29,48,48,48] (by decide +kernel)

private theorem m2_10 : availableMass (start .one3wide) ⟨34,3,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨34,3,0⟩ 11 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨34,3,0⟩ 11 286 [11,13,15,17,20,25,41,48,48,48] (by decide +kernel)

private theorem m2_11 : availableMass (start .one3wide) ⟨35,6,0⟩ 29 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨35,6,0⟩ 29 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨35,6,0⟩ 29 212 [7,7,7,8,3,3,3,4,4,4,4,4,4,5,5,5,6,6,7,8,10,13,37,48] (by decide +kernel)

private theorem m2_12 : availableMass (start .one3wide) ⟨38,18,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨38,18,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨38,18,0⟩ 46 124 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,3,3,3,4,4,5,7,16] (by decide +kernel)

private theorem m2_13 : availableMass (start .one3wide) ⟨50,3,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨50,3,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨50,3,0⟩ 15 290 [15,22,26,35,48,48,48,48] (by decide +kernel)

private theorem m2_14 : availableMass (start .one3wide) ⟨66,3,0⟩ 19 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,3,0⟩ 19 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨66,3,0⟩ 19 294 [19,20,25,38,48,48,48,48] (by decide +kernel)

private theorem m2_15 : availableMass (start .one3wide) ⟨66,16,0⟩ 40 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,16,0⟩ 40 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨66,16,0⟩ 40 126 [20,20,6,7,8,11,15,39] (by decide +kernel)

private theorem m2_16 : availableMass (start .one3wide) ⟨66,28,0⟩ 47 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,28,0⟩ 47 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨66,28,0⟩ 47 100 [15,16,16,4,5,6,7,10,21] (by decide +kernel)

private theorem m2_17 : availableMass (start .one3wide) ⟨66,41,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨66,41,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨66,41,0⟩ 51 88 [12,13,13,13,3,3,4,5,7,15] (by decide +kernel)

private theorem m2_18 : availableMass (start .one3wide) ⟨67,6,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨67,6,0⟩ 37 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨67,6,0⟩ 37 220 [12,12,13,6,7,7,8,10,12,37,48,48] (by decide +kernel)

private theorem m2_19 : availableMass (start .one3wide) ⟨67,42,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨67,42,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨67,42,0⟩ 55 91 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,4,9] (by decide +kernel)

private theorem m2_20 : availableMass (start .one3wide) ⟨68,12,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨68,12,0⟩ 38 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨68,12,0⟩ 38 148 [19,19,7,9,10,14,22,48] (by decide +kernel)

private theorem m2_21 : availableMass (start .one3wide) ⟨68,34,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨68,34,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨68,34,0⟩ 51 95 [8,8,8,9,9,9,3,3,3,3,4,5,7,16] (by decide +kernel)

private theorem m2_22 : availableMass (start .one3wide) ⟨69,45,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨69,45,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨69,45,0⟩ 56 90 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,6] (by decide +kernel)

private theorem m2_23 : availableMass (start .one3wide) ⟨70,24,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨70,24,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨70,24,0⟩ 50 111 [5,5,5,5,6,6,6,6,6,2,2,2,2,2,2,3,3,3,4,4,5,8,19] (by decide +kernel)

private theorem m2_24 : availableMass (start .one3wide) ⟨71,33,0⟩ 52 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨71,33,0⟩ 52 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨71,33,0⟩ 52 97 [6,6,6,6,7,7,7,7,2,2,2,2,2,3,3,4,5,6,14] (by decide +kernel)

private theorem m2_25 : availableMass (start .one3wide) ⟨72,36,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨72,36,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨72,36,0⟩ 53 95 [5,5,5,5,5,5,5,6,6,6,2,2,2,2,2,3,3,3,4,6,13] (by decide +kernel)

private theorem m2_26 : availableMass (start .one3wide) ⟨83,3,0⟩ 23 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨83,3,0⟩ 23 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨83,3,0⟩ 23 298 [23,17,21,45,48,48,48,48] (by decide +kernel)

private theorem m2_27 : availableMass (start .one3wide) ⟨83,6,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨83,6,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨83,6,0⟩ 44 227 [7,7,7,7,8,8,3,3,3,3,3,4,4,4,4,5,6,45,48,48] (by decide +kernel)

private theorem m2_28 : availableMass (start .one3wide) ⟨84,43,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨84,43,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨84,43,0⟩ 56 91 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,6] (by decide +kernel)

private theorem m2_29 : availableMass (start .one3wide) ⟨99,3,0⟩ 27 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨99,3,0⟩ 27 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨99,3,0⟩ 27 302 [27,16,19,48,48,48,48,48] (by decide +kernel)

private theorem m2_30 : availableMass (start .one3wide) ⟨99,9,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨99,9,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨99,9,0⟩ 49 186 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,3,7,48,48] (by decide +kernel)

private theorem m2_31 : availableMass (start .one3wide) ⟨100,12,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨100,12,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨100,12,0⟩ 50 160 [2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,4,26,48] (by decide +kernel)

private theorem m2_32 : availableMass (start .one3wide) ⟨100,37,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨100,37,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨100,37,0⟩ 54 95 [4,5,5,5,5,5,5,5,5,5,5,1,1,2,2,2,2,2,3,3,4,6,13] (by decide +kernel)

private theorem m2_33 : availableMass (start .one3wide) ⟨101,42,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨101,42,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨101,42,0⟩ 56 92 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,7] (by decide +kernel)

private theorem m2_34 : availableMass (start .one3wide) ⟨101,50,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨101,50,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨101,50,0⟩ 57 88 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,6] (by decide +kernel)

private theorem m2_35 : availableMass (start .one3wide) ⟨102,39,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨102,39,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨102,39,0⟩ 55 94 [3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,1,1,1,1,1,1,1,1,1,2,2,2,2,3,3,5,11] (by decide +kernel)

private theorem m2_36 : availableMass (start .one3wide) ⟨104,49,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨104,49,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨104,49,0⟩ 57 88 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m2_37 : availableMass (start .one3wide) ⟨114,48,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨114,48,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨114,48,0⟩ 57 89 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,7] (by decide +kernel)

private theorem m2_38 : availableMass (start .one3wide) ⟨115,3,0⟩ 30 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨115,3,0⟩ 30 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨115,3,0⟩ 30 305 [30,16,19,48,48,48,48,48] (by decide +kernel)

private theorem m2_39 : availableMass (start .one3wide) ⟨115,31,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨115,31,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨115,31,0⟩ 51 99 [10,10,10,10,11,3,4,5,6,8,22] (by decide +kernel)

private theorem m2_40 : availableMass (start .one3wide) ⟨115,36,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨115,36,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨115,36,0⟩ 55 97 [3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,3,5,13] (by decide +kernel)

private theorem m2_41 : availableMass (start .one3wide) ⟨116,25,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨116,25,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨116,25,0⟩ 54 112 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,27] (by decide +kernel)

private theorem m2_42 : availableMass (start .one3wide) ⟨116,41,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨116,41,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨116,41,0⟩ 56 93 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,10] (by decide +kernel)

private theorem m2_43 : availableMass (start .one3wide) ⟨118,47,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨118,47,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨118,47,0⟩ 57 90 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m2_44 : availableMass (start .one3wide) ⟨124,39,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨124,39,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨124,39,0⟩ 56 95 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,11] (by decide +kernel)

private theorem m2_45 : availableMass (start .one3wide) ⟨126,46,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one3wide) ⟨126,46,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one3wide) ⟨126,46,0⟩ 57 90 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,8] (by decide +kernel)

private theorem m3_0 : availableMass (start .one4) ⟨2,6,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one4) ⟨2,6,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨2,6,0⟩ 15 180 [7,8,4,4,4,5,5,5,5,5,6,6,6,7,7,8,8,9,10,13,17,31] (by decide +kernel)

private theorem m3_1 : availableMass (start .one4) ⟨3,9,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .one4) ⟨3,9,0⟩ 33 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨3,9,0⟩ 33 159 [2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,4,4,5,5,7,9,20] (by decide +kernel)

private theorem m3_2 : availableMass (start .one4) ⟨6,18,0⟩ 45 < layerNeed := by
  rw [mass_eq (start .one4) ⟨6,18,0⟩ 45 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨6,18,0⟩ 45 120 [9,9,9,9,9,4,4,4,5,5,6,6,8,11,22] (by decide +kernel)

private theorem m3_3 : availableMass (start .one4) ⟨9,27,0⟩ 53 < layerNeed := by
  rw [mass_eq (start .one4) ⟨9,27,0⟩ 53 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨9,27,0⟩ 53 106 [5,5,5,5,5,5,5,6,6,6,2,2,2,3,3,3,3,4,4,5,7,15] (by decide +kernel)

private theorem m3_4 : availableMass (start .one4) ⟨10,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one4) ⟨10,3,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨10,3,0⟩ 1 236 [1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,5,5,5,6,6,7,8,9,11,15,26] (by decide +kernel)

private theorem m3_5 : availableMass (start .one4) ⟨12,36,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one4) ⟨12,36,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨12,36,0⟩ 55 96 [6,7,7,7,7,7,7,7,3,3,3,3,4,5,6,14] (by decide +kernel)

private theorem m3_6 : availableMass (start .one4) ⟨18,3,0⟩ 7 < layerNeed := by
  rw [mass_eq (start .one4) ⟨18,3,0⟩ 7 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨18,3,0⟩ 7 242 [7,6,6,6,7,7,7,8,8,9,10,11,12,14,17,23,36,48] (by decide +kernel)

private theorem m3_7 : availableMass (start .one4) ⟨34,3,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .one4) ⟨34,3,0⟩ 11 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨34,3,0⟩ 11 246 [11,17,19,23,32,48,48,48] (by decide +kernel)

private theorem m3_8 : availableMass (start .one4) ⟨35,6,0⟩ 31 < layerNeed := by
  rw [mass_eq (start .one4) ⟨35,6,0⟩ 31 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨35,6,0⟩ 31 196 [10,10,11,6,6,7,7,8,9,11,13,18,32,48] (by decide +kernel)

private theorem m3_9 : availableMass (start .one4) ⟨37,15,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one4) ⟨37,15,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨37,15,0⟩ 49 135 [2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,4,5,6,9,20] (by decide +kernel)

private theorem m3_10 : availableMass (start .one4) ⟨50,3,0⟩ 15 < layerNeed := by
  rw [mass_eq (start .one4) ⟨50,3,0⟩ 15 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨50,3,0⟩ 15 250 [15,22,28,41,48,48,48] (by decide +kernel)

private theorem m3_11 : availableMass (start .one4) ⟨66,3,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .one4) ⟨66,3,0⟩ 20 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨66,3,0⟩ 20 255 [20,20,26,45,48,48,48] (by decide +kernel)

private theorem m3_12 : availableMass (start .one4) ⟨67,6,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .one4) ⟨67,6,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨67,6,0⟩ 46 211 [5,5,5,5,5,5,5,5,6,2,2,3,3,3,3,3,3,3,3,4,4,4,5,6,18,48,48] (by decide +kernel)

private theorem m3_13 : availableMass (start .one4) ⟨68,42,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one4) ⟨68,42,0⟩ 58 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨68,42,0⟩ 58 93 [5,5,6,6,6,6,6,6,6,6,2,2,2,3,3,4,6,13] (by decide +kernel)

private theorem m3_14 : availableMass (start .one4) ⟨70,27,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one4) ⟨70,27,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨70,27,0⟩ 57 110 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,4,6,15] (by decide +kernel)

private theorem m3_15 : availableMass (start .one4) ⟨70,38,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one4) ⟨70,38,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨70,38,0⟩ 59 98 [3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,1,1,1,1,1,1,2,2,2,2,2,3,3,5,12] (by decide +kernel)

private theorem m3_16 : availableMass (start .one4) ⟨72,39,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one4) ⟨72,39,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨72,39,0⟩ 60 98 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,9] (by decide +kernel)

private theorem m3_17 : availableMass (start .one4) ⟨72,44,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one4) ⟨72,44,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨72,44,0⟩ 61 95 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,8] (by decide +kernel)

private theorem m3_18 : availableMass (start .one4) ⟨83,3,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .one4) ⟨83,3,0⟩ 24 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨83,3,0⟩ 24 259 [24,19,24,48,48,48,48] (by decide +kernel)

private theorem m3_19 : availableMass (start .one4) ⟨99,3,0⟩ 28 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,3,0⟩ 28 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨99,3,0⟩ 28 263 [28,19,24,48,48,48,48] (by decide +kernel)

private theorem m3_20 : availableMass (start .one4) ⟨99,9,0⟩ 51 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,9,0⟩ 51 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨99,9,0⟩ 51 177 [7,7,7,7,7,8,8,3,3,4,4,4,5,5,7,43,48] (by decide +kernel)

private theorem m3_21 : availableMass (start .one4) ⟨99,18,0⟩ 55 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,18,0⟩ 55 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨99,18,0⟩ 55 130 [4,4,4,4,4,5,5,5,5,5,5,5,2,2,2,2,2,2,3,3,3,4,5,6,39] (by decide +kernel)

private theorem m3_22 : availableMass (start .one4) ⟨99,29,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one4) ⟨99,29,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨99,29,0⟩ 59 109 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,15] (by decide +kernel)

private theorem m3_23 : availableMass (start .one4) ⟨100,22,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one4) ⟨100,22,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨100,22,0⟩ 56 119 [4,4,4,4,4,4,4,4,4,5,5,5,5,2,2,2,2,2,2,2,3,3,4,5,6,28] (by decide +kernel)

private theorem m3_24 : availableMass (start .one4) ⟨102,36,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one4) ⟨102,36,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨102,36,0⟩ 60 101 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,5,12] (by decide +kernel)

private theorem m3_25 : availableMass (start .one4) ⟨109,49,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨109,49,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨109,49,0⟩ 62 93 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,8] (by decide +kernel)

private theorem m3_26 : availableMass (start .one4) ⟨110,39,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one4) ⟨110,39,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨110,39,0⟩ 61 99 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,10] (by decide +kernel)

private theorem m3_27 : availableMass (start .one4) ⟨115,3,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .one4) ⟨115,3,0⟩ 32 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨115,3,0⟩ 32 267 [32,19,24,48,48,48,48] (by decide +kernel)

private theorem m3_28 : availableMass (start .one4) ⟨115,16,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one4) ⟨115,16,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨115,16,0⟩ 57 139 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,5,48] (by decide +kernel)

private theorem m3_29 : availableMass (start .one4) ⟨115,20,0⟩ 58 < layerNeed := by
  rw [mass_eq (start .one4) ⟨115,20,0⟩ 58 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨115,20,0⟩ 58 126 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,36] (by decide +kernel)

private theorem m3_30 : availableMass (start .one4) ⟨117,48,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨117,48,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨117,48,0⟩ 62 93 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,7] (by decide +kernel)

private theorem m3_31 : availableMass (start .one4) ⟨124,47,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨124,47,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨124,47,0⟩ 62 94 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,8] (by decide +kernel)

private theorem m3_32 : availableMass (start .one4) ⟨128,46,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one4) ⟨128,46,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one4) ⟨128,46,0⟩ 62 95 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,9] (by decide +kernel)

private theorem m4_0 : availableMass (start .one5) ⟨1,3,0⟩ 1 < layerNeed := by
  rw [mass_eq (start .one5) ⟨1,3,0⟩ 1 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨1,3,0⟩ 1 207 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,4,4,4,4,5,5,6,7,10,17] (by decide +kernel)

private theorem m4_1 : availableMass (start .one5) ⟨2,6,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .one5) ⟨2,6,0⟩ 16 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨2,6,0⟩ 16 166 [16,9,10,10,11,13,15,17,23,42] (by decide +kernel)

private theorem m4_2 : availableMass (start .one5) ⟨3,9,0⟩ 33 < layerNeed := by
  rw [mass_eq (start .one5) ⟨3,9,0⟩ 33 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨3,9,0⟩ 33 150 [11,11,11,7,7,8,9,9,11,13,18,35] (by decide +kernel)

private theorem m4_3 : availableMass (start .one5) ⟨5,15,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one5) ⟨5,15,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨5,15,0⟩ 49 131 [7,7,7,7,7,7,7,4,4,4,4,5,5,6,7,8,11,24] (by decide +kernel)

private theorem m4_4 : availableMass (start .one5) ⟨8,24,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one5) ⟨8,24,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨8,24,0⟩ 59 115 [3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,2,2,2,2,2,2,3,3,3,3,4,5,7,16] (by decide +kernel)

private theorem m4_5 : availableMass (start .one5) ⟨10,3,0⟩ 3 < layerNeed := by
  rw [mass_eq (start .one5) ⟨10,3,0⟩ 3 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨10,3,0⟩ 3 209 [3,7,7,8,8,9,9,10,11,12,14,16,20,27,48] (by decide +kernel)

private theorem m4_6 : availableMass (start .one5) ⟨18,3,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one5) ⟨18,3,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨18,3,0⟩ 21 227 [3,3,3,4,4,4,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,5,5,5,5,6,6,7,8,9,11,14,20,45] (by decide +kernel)

private theorem m4_7 : availableMass (start .one5) ⟨34,3,0⟩ 32 < layerNeed := by
  rw [mass_eq (start .one5) ⟨34,3,0⟩ 32 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨34,3,0⟩ 32 238 [6,6,6,7,7,5,5,5,6,6,6,7,8,8,9,11,14,20,48,48] (by decide +kernel)

private theorem m4_8 : availableMass (start .one5) ⟨50,3,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one5) ⟨50,3,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨50,3,0⟩ 43 249 [5,5,5,5,5,6,6,6,3,3,4,4,4,4,4,5,5,5,6,6,7,9,41,48,48] (by decide +kernel)

private theorem m4_9 : availableMass (start .one5) ⟨67,6,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .one5) ⟨67,6,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨67,6,0⟩ 49 199 [8,8,8,8,8,9,4,4,5,5,5,6,7,8,10,48,48] (by decide +kernel)

private theorem m4_10 : availableMass (start .one5) ⟨68,42,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one5) ⟨68,42,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨68,42,0⟩ 60 95 [9,10,10,10,10,11,4,6,8,17] (by decide +kernel)

private theorem m4_11 : availableMass (start .one5) ⟨69,21,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .one5) ⟨69,21,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨69,21,0⟩ 62 125 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,4,7,20] (by decide +kernel)

private theorem m4_12 : availableMass (start .one5) ⟨71,41,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .one5) ⟨71,41,0⟩ 66 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨71,41,0⟩ 66 101 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,2,2,2,2,3,4,12] (by decide +kernel)

private theorem m4_13 : availableMass (start .one5) ⟨72,36,0⟩ 66 < layerNeed := by
  rw [mass_eq (start .one5) ⟨72,36,0⟩ 66 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨72,36,0⟩ 66 106 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,12] (by decide +kernel)

private theorem m4_14 : availableMass (start .one5) ⟨99,6,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .one5) ⟨99,6,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨99,6,0⟩ 57 207 [4,4,4,5,5,5,5,5,5,5,5,5,2,2,3,3,3,3,3,3,4,4,5,19,48,48] (by decide +kernel)

private theorem m4_15 : availableMass (start .one5) ⟨99,15,0⟩ 60 < layerNeed := by
  rw [mass_eq (start .one5) ⟨99,15,0⟩ 60 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨99,15,0⟩ 60 142 [4,4,4,4,4,4,4,4,4,4,5,5,5,5,2,2,2,2,3,3,3,3,4,5,7,46] (by decide +kernel)

private theorem m4_16 : availableMass (start .one5) ⟨99,39,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .one5) ⟨99,39,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨99,39,0⟩ 67 104 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,11] (by decide +kernel)

private theorem m4_17 : availableMass (start .one5) ⟨101,27,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .one5) ⟨101,27,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨101,27,0⟩ 65 116 [1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,3,5,18] (by decide +kernel)

private theorem m4_18 : availableMass (start .one5) ⟨101,45,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨101,45,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨101,45,0⟩ 68 101 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,10] (by decide +kernel)

private theorem m4_19 : availableMass (start .one5) ⟨116,38,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .one5) ⟨116,38,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨116,38,0⟩ 67 105 [1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,12] (by decide +kernel)

private theorem m4_20 : availableMass (start .one5) ⟨116,42,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨116,42,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨116,42,0⟩ 68 103 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,10] (by decide +kernel)

private theorem m4_21 : availableMass (start .one5) ⟨124,41,0⟩ 68 < layerNeed := by
  rw [mass_eq (start .one5) ⟨124,41,0⟩ 68 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one5) ⟨124,41,0⟩ 68 103 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,10] (by decide +kernel)

private theorem m5_0 : availableMass (start .one6) ⟨1,3,0⟩ 21 < layerNeed := by
  rw [mass_eq (start .one6) ⟨1,3,0⟩ 21 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨1,3,0⟩ 21 204 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,4,5,6,8,21] (by decide +kernel)

private theorem m5_1 : availableMass (start .one6) ⟨2,6,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .one6) ⟨2,6,0⟩ 41 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨2,6,0⟩ 41 178 [3,3,3,4,4,4,4,4,4,4,4,3,3,3,3,3,3,3,4,4,4,4,4,4,5,5,5,6,7,8,10,13,33] (by decide +kernel)

private theorem m5_2 : availableMass (start .one6) ⟨4,12,0⟩ 54 < layerNeed := by
  rw [mass_eq (start .one6) ⟨4,12,0⟩ 54 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨4,12,0⟩ 54 145 [5,6,6,6,6,6,6,6,7,4,5,5,5,6,6,7,9,13,31] (by decide +kernel)

private theorem m5_3 : availableMass (start .one6) ⟨7,21,0⟩ 63 < layerNeed := by
  rw [mass_eq (start .one6) ⟨7,21,0⟩ 63 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨7,21,0⟩ 63 124 [6,6,6,6,6,6,6,7,7,7,4,4,4,5,5,7,9,23] (by decide +kernel)

private theorem m5_4 : availableMass (start .one6) ⟨9,27,0⟩ 69 < layerNeed := by
  rw [mass_eq (start .one6) ⟨9,27,0⟩ 69 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨9,27,0⟩ 69 119 [4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,5,2,2,2,3,3,3,4,5,7,19] (by decide +kernel)

private theorem m5_5 : availableMass (start .one6) ⟨34,3,0⟩ 43 < layerNeed := by
  rw [mass_eq (start .one6) ⟨34,3,0⟩ 43 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨34,3,0⟩ 43 226 [5,5,5,5,5,6,6,6,4,4,4,4,4,5,5,5,6,6,7,8,9,12,16,36,48] (by decide +kernel)

private theorem m5_6 : availableMass (start .one6) ⟨66,3,0⟩ 56 < layerNeed := by
  rw [mass_eq (start .one6) ⟨66,3,0⟩ 56 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨66,3,0⟩ 56 239 [5,5,5,5,6,6,6,6,6,6,4,4,4,4,5,5,5,6,7,8,35,48,48] (by decide +kernel)

private theorem m5_7 : availableMass (start .one6) ⟨69,18,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .one6) ⟨69,18,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨69,18,0⟩ 65 133 [5,5,6,6,6,6,6,6,6,6,7,3,4,4,5,5,7,10,30] (by decide +kernel)

private theorem m5_8 : availableMass (start .one6) ⟨69,34,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .one6) ⟨69,34,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨69,34,0⟩ 75 116 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,14] (by decide +kernel)

private theorem m5_9 : availableMass (start .one6) ⟨99,6,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one6) ⟨99,6,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨99,6,0⟩ 59 196 [8,8,8,8,9,9,9,6,6,8,9,12,48,48] (by decide +kernel)

private theorem m5_10 : availableMass (start .one6) ⟨99,15,0⟩ 61 < layerNeed := by
  rw [mass_eq (start .one6) ⟨99,15,0⟩ 61 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨99,15,0⟩ 61 139 [9,10,10,10,11,11,6,7,8,13,44] (by decide +kernel)

private theorem m5_11 : availableMass (start .one6) ⟨99,27,0⟩ 70 < layerNeed := by
  rw [mass_eq (start .one6) ⟨99,27,0⟩ 70 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨99,27,0⟩ 70 120 [5,5,5,5,5,5,5,5,6,6,6,6,6,2,2,3,3,4,5,8,23] (by decide +kernel)

private theorem m5_12 : availableMass (start .one6) ⟨100,21,0⟩ 73 < layerNeed := by
  rw [mass_eq (start .one6) ⟨100,21,0⟩ 73 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨100,21,0⟩ 73 134 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,4,6,25] (by decide +kernel)

private theorem m5_13 : availableMass (start .one6) ⟨101,27,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .one6) ⟨101,27,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨101,27,0⟩ 75 125 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,18] (by decide +kernel)

private theorem m5_14 : availableMass (start .one6) ⟨115,39,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .one6) ⟨115,39,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one6) ⟨115,39,0⟩ 77 113 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,13] (by decide +kernel)

private theorem m6_0 : availableMass (start .one7) ⟨1,3,0⟩ 20 < layerNeed := by
  rw [mass_eq (start .one7) ⟨1,3,0⟩ 20 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨1,3,0⟩ 20 185 [10,10,9,9,10,10,11,13,15,18,24,46] (by decide +kernel)

private theorem m6_1 : availableMass (start .one7) ⟨2,6,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .one7) ⟨2,6,0⟩ 38 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨2,6,0⟩ 38 164 [12,13,13,11,12,14,17,24,48] (by decide +kernel)

private theorem m6_2 : availableMass (start .one7) ⟨3,9,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .one7) ⟨3,9,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨3,9,0⟩ 59 162 [8,8,8,8,9,9,9,7,7,8,10,12,17,42] (by decide +kernel)

private theorem m6_3 : availableMass (start .one7) ⟨6,18,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .one7) ⟨6,18,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨6,18,0⟩ 65 131 [10,10,10,11,12,12,8,10,14,34] (by decide +kernel)

private theorem m6_4 : availableMass (start .one7) ⟨7,21,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .one7) ⟨7,21,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨7,21,0⟩ 79 137 [5,5,5,5,5,5,5,6,6,6,6,6,7,7,4,5,5,7,10,27] (by decide +kernel)

private theorem m6_5 : availableMass (start .one7) ⟨11,33,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .one7) ⟨11,33,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨11,33,0⟩ 94 135 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,18] (by decide +kernel)

private theorem m6_6 : availableMass (start .one7) ⟨34,3,0⟩ 41 < layerNeed := by
  rw [mass_eq (start .one7) ⟨34,3,0⟩ 41 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨34,3,0⟩ 41 206 [13,14,14,10,11,13,16,23,44,48] (by decide +kernel)

private theorem m6_7 : availableMass (start .one7) ⟨34,6,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .one7) ⟨34,6,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨34,6,0⟩ 79 205 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m6_8 : availableMass (start .one7) ⟨37,18,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .one7) ⟨37,18,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨37,18,0⟩ 90 156 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,5,28] (by decide +kernel)

private theorem m6_9 : availableMass (start .one7) ⟨66,3,0⟩ 63 < layerNeed := by
  rw [mass_eq (start .one7) ⟨66,3,0⟩ 63 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨66,3,0⟩ 63 228 [8,8,9,9,9,10,10,7,7,9,10,13,23,48,48] (by decide +kernel)

private theorem m6_10 : availableMass (start .one7) ⟨68,15,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .one7) ⟨68,15,0⟩ 86 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨68,15,0⟩ 86 161 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,2,2,2,2,2,3,3,3,4,6,9,35] (by decide +kernel)

private theorem m6_11 : availableMass (start .one7) ⟨68,32,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .one7) ⟨68,32,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨68,32,0⟩ 94 136 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,19] (by decide +kernel)

private theorem m6_12 : availableMass (start .one7) ⟨98,3,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .one7) ⟨98,3,0⟩ 86 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .one7) ⟨98,3,0⟩ 86 251 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,3,34,48,48] (by decide +kernel)

private theorem m7_0 : availableMass (start .two6thin) ⟨1,3,0⟩ 11 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨1,3,0⟩ 11 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨1,3,0⟩ 11 194 [5,6,4,5,5,5,5,5,5,6,6,6,6,7,7,7,8,9,10,11,14,18,34] (by decide +kernel)

private theorem m7_1 : availableMass (start .two6thin) ⟨2,6,0⟩ 46 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨2,6,0⟩ 46 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨2,6,0⟩ 46 183 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m7_2 : availableMass (start .two6thin) ⟨4,12,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨4,12,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨4,12,0⟩ 62 153 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,3,4,5,24] (by decide +kernel)

private theorem m7_3 : availableMass (start .two6thin) ⟨8,24,0⟩ 64 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨8,24,0⟩ 64 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨8,24,0⟩ 64 119 [6,7,7,7,7,7,7,8,8,4,4,5,5,6,9,22] (by decide +kernel)

private theorem m7_4 : availableMass (start .two6thin) ⟨10,30,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨10,30,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨10,30,0⟩ 72 117 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,2,2,2,2,2,2,2,3,3,5,16] (by decide +kernel)

private theorem m7_5 : availableMass (start .two6thin) ⟨18,3,0⟩ 24 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨18,3,0⟩ 24 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨18,3,0⟩ 24 207 [8,8,8,7,8,9,9,10,11,13,16,21,31,48] (by decide +kernel)

private theorem m7_6 : availableMass (start .two6thin) ⟨34,3,0⟩ 37 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨34,3,0⟩ 37 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨34,3,0⟩ 37 220 [9,9,9,10,6,7,7,8,9,10,12,15,20,41,48] (by decide +kernel)

private theorem m7_7 : availableMass (start .two6thin) ⟨50,3,0⟩ 50 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨50,3,0⟩ 50 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨50,3,0⟩ 50 233 [6,6,6,6,6,6,7,7,4,4,4,5,5,5,6,7,7,9,11,20,48,48] (by decide +kernel)

private theorem m7_8 : availableMass (start .two6thin) ⟨69,21,0⟩ 71 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨69,21,0⟩ 71 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨69,21,0⟩ 71 132 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,2,2,2,2,2,2,3,3,3,4,7,23] (by decide +kernel)

private theorem m7_9 : availableMass (start .two6thin) ⟨70,39,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨70,39,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨70,39,0⟩ 76 112 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,13] (by decide +kernel)

private theorem m7_10 : availableMass (start .two6thin) ⟨99,6,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨99,6,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨99,6,0⟩ 67 204 [2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,7,48,48] (by decide +kernel)

private theorem m7_11 : availableMass (start .two6thin) ⟨99,15,0⟩ 69 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨99,15,0⟩ 69 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨99,15,0⟩ 69 147 [3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,2,2,2,2,2,3,3,3,4,5,8,42] (by decide +kernel)

private theorem m7_12 : availableMass (start .two6thin) ⟨101,27,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨101,27,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨101,27,0⟩ 75 125 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,18] (by decide +kernel)

private theorem m7_13 : availableMass (start .two6thin) ⟨101,44,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨101,44,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨101,44,0⟩ 77 110 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,12] (by decide +kernel)

private theorem m7_14 : availableMass (start .two6thin) ⟨116,40,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨116,40,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨116,40,0⟩ 77 112 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4,13] (by decide +kernel)

private theorem m7_15 : availableMass (start .two6thin) ⟨128,48,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thin) ⟨128,48,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thin) ⟨128,48,0⟩ 78 108 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m8_0 : availableMass (start .two6thinwide) ⟨1,3,0⟩ 16 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨1,3,0⟩ 16 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨1,3,0⟩ 16 199 [5,5,6,4,4,5,5,5,5,5,5,6,6,6,7,7,7,8,9,10,11,14,18,36] (by decide +kernel)

private theorem m8_1 : availableMass (start .two6thinwide) ⟨2,6,0⟩ 25 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨2,6,0⟩ 25 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨2,6,0⟩ 25 162 [12,13,10,11,13,15,18,24,46] (by decide +kernel)

private theorem m8_2 : availableMass (start .two6thinwide) ⟨3,9,0⟩ 57 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨3,9,0⟩ 57 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨3,9,0⟩ 57 167 [2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,4,4,4,5,6,7,10,31] (by decide +kernel)

private theorem m8_3 : availableMass (start .two6thinwide) ⟨10,28,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨10,28,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨10,28,0⟩ 59 107 [14,14,15,16,6,8,11,23] (by decide +kernel)

private theorem m8_4 : availableMass (start .two6thinwide) ⟨10,30,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨10,30,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨10,30,0⟩ 76 121 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,5,15] (by decide +kernel)

private theorem m8_5 : availableMass (start .two6thinwide) ⟨17,3,0⟩ 35 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨17,3,0⟩ 35 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨17,3,0⟩ 35 218 [4,4,4,4,4,5,5,5,4,4,4,4,4,4,5,5,5,5,6,6,7,7,8,9,11,15,22,48] (by decide +kernel)

private theorem m8_6 : availableMass (start .two6thinwide) ⟨34,6,0⟩ 49 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨34,6,0⟩ 49 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨34,6,0⟩ 49 186 [7,8,8,8,9,9,6,7,7,8,9,12,15,25,48] (by decide +kernel)

private theorem m8_7 : availableMass (start .two6thinwide) ⟨38,21,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨38,21,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨38,21,0⟩ 72 133 [3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,2,2,2,2,2,2,3,3,3,4,5,8,23] (by decide +kernel)

private theorem m8_8 : availableMass (start .two6thinwide) ⟨39,39,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨39,39,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨39,39,0⟩ 77 113 [2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,2,2,2,2,3,3,5,14] (by decide +kernel)

private theorem m8_9 : availableMass (start .two6thinwide) ⟨65,15,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨65,15,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨65,15,0⟩ 62 140 [8,8,8,9,9,10,10,5,6,7,9,13,38] (by decide +kernel)

private theorem m8_10 : availableMass (start .two6thinwide) ⟨66,6,0⟩ 62 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,6,0⟩ 62 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨66,6,0⟩ 62 199 [5,5,5,5,5,5,5,5,5,5,6,6,4,4,4,4,5,5,6,7,10,40,48] (by decide +kernel)

private theorem m8_11 : availableMass (start .two6thinwide) ⟨66,9,0⟩ 70 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,9,0⟩ 70 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨66,9,0⟩ 70 180 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,3,3,4,12,48] (by decide +kernel)

private theorem m8_12 : availableMass (start .two6thinwide) ⟨66,17,0⟩ 74 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,17,0⟩ 74 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨66,17,0⟩ 74 145 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,4,6,25] (by decide +kernel)

private theorem m8_13 : availableMass (start .two6thinwide) ⟨66,39,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,39,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨66,39,0⟩ 79 115 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,13] (by decide +kernel)

private theorem m8_14 : availableMass (start .two6thinwide) ⟨66,40,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨66,40,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨66,40,0⟩ 80 115 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,12] (by decide +kernel)

private theorem m8_15 : availableMass (start .two6thinwide) ⟨67,24,0⟩ 75 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨67,24,0⟩ 75 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨67,24,0⟩ 75 130 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,2,2,2,2,2,2,3,3,4,7,22] (by decide +kernel)

private theorem m8_16 : availableMass (start .two6thinwide) ⟨70,30,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨70,30,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨70,30,0⟩ 77 122 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,1,1,1,1,1,1,1,1,2,2,2,2,3,4,5,17] (by decide +kernel)

private theorem m8_17 : availableMass (start .two6thinwide) ⟨82,39,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨82,39,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨82,39,0⟩ 80 116 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,13] (by decide +kernel)

private theorem m8_18 : availableMass (start .two6thinwide) ⟨84,38,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨84,38,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨84,38,0⟩ 78 115 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,2,2,2,2,3,5,15] (by decide +kernel)

private theorem m8_19 : availableMass (start .two6thinwide) ⟨88,48,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨88,48,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨88,48,0⟩ 81 111 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,11] (by decide +kernel)

private theorem m8_20 : availableMass (start .two6thinwide) ⟨90,47,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨90,47,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨90,47,0⟩ 81 112 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,11] (by decide +kernel)

private theorem m8_21 : availableMass (start .two6thinwide) ⟨92,46,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨92,46,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨92,46,0⟩ 81 112 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,11] (by decide +kernel)

private theorem m8_22 : availableMass (start .two6thinwide) ⟨93,45,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨93,45,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨93,45,0⟩ 81 113 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m8_23 : availableMass (start .two6thinwide) ⟨97,3,0⟩ 38 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨97,3,0⟩ 38 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨97,3,0⟩ 38 221 [38,17,22,48,48,48] (by decide +kernel)

private theorem m8_24 : availableMass (start .two6thinwide) ⟨98,12,0⟩ 74 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,12,0⟩ 74 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨98,12,0⟩ 74 165 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,10,48] (by decide +kernel)

private theorem m8_25 : availableMass (start .two6thinwide) ⟨98,28,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,28,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨98,28,0⟩ 77 125 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,2,2,2,2,2,3,4,6,19] (by decide +kernel)

private theorem m8_26 : availableMass (start .two6thinwide) ⟨98,33,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,33,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨98,33,0⟩ 78 120 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,1,1,1,1,1,1,1,1,2,2,2,3,3,5,17] (by decide +kernel)

private theorem m8_27 : availableMass (start .two6thinwide) ⟨98,38,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨98,38,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨98,38,0⟩ 79 116 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,1,1,1,1,1,1,1,1,1,2,2,2,3,4,15] (by decide +kernel)

private theorem m8_28 : availableMass (start .two6thinwide) ⟨99,31,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨99,31,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨99,31,0⟩ 79 123 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,17] (by decide +kernel)

private theorem m8_29 : availableMass (start .two6thinwide) ⟨99,36,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨99,36,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨99,36,0⟩ 80 119 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4,14] (by decide +kernel)

private theorem m8_30 : availableMass (start .two6thinwide) ⟨103,44,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨103,44,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨103,44,0⟩ 81 114 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m8_31 : availableMass (start .two6thinwide) ⟨112,43,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨112,43,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨112,43,0⟩ 81 114 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m8_32 : availableMass (start .two6thinwide) ⟨113,3,0⟩ 44 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨113,3,0⟩ 44 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨113,3,0⟩ 44 227 [21,23,17,22,48,48,48] (by decide +kernel)

private theorem m8_33 : availableMass (start .two6thinwide) ⟨113,27,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨113,27,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨113,27,0⟩ 79 129 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,20] (by decide +kernel)

private theorem m8_34 : availableMass (start .two6thinwide) ⟨114,25,0⟩ 77 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨114,25,0⟩ 77 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨114,25,0⟩ 77 130 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,2,2,2,2,2,3,4,6,24] (by decide +kernel)

private theorem m8_35 : availableMass (start .two6thinwide) ⟨118,33,0⟩ 80 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨118,33,0⟩ 80 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨118,33,0⟩ 80 122 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m8_36 : availableMass (start .two6thinwide) ⟨121,42,0⟩ 81 < layerNeed := by
  rw [mass_eq (start .two6thinwide) ⟨121,42,0⟩ 81 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6thinwide) ⟨121,42,0⟩ 81 115 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m9_0 : availableMass (start .two6wide) ⟨1,3,0⟩ 42 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨1,3,0⟩ 42 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨1,3,0⟩ 42 225 [4,4,4,5,5,5,5,5,5,5,5,5,5,5,6,6,6,7,7,8,9,10,12,16,23,48] (by decide +kernel)

private theorem m9_1 : availableMass (start .two6wide) ⟨3,9,0⟩ 67 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨3,9,0⟩ 67 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨3,9,0⟩ 67 177 [6,6,6,6,6,7,7,7,8,8,6,6,7,8,10,12,17,44] (by decide +kernel)

private theorem m9_2 : availableMass (start .two6wide) ⟨6,18,0⟩ 87 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨6,18,0⟩ 87 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨6,18,0⟩ 87 155 [3,4,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,6,3,4,4,5,5,7,10,30] (by decide +kernel)

private theorem m9_3 : availableMass (start .two6wide) ⟨9,27,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨9,27,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨9,27,0⟩ 92 142 [3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,6,3,3,4,4,5,8,23] (by decide +kernel)

private theorem m9_4 : availableMass (start .two6wide) ⟨10,28,0⟩ 99 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨10,28,0⟩ 99 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨10,28,0⟩ 99 147 [1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,1,1,1,1,2,2,2,2,2,2,3,3,5,21] (by decide +kernel)

private theorem m9_5 : availableMass (start .two6wide) ⟨11,31,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨11,31,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨11,31,0⟩ 101 145 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,2,2,2,2,2,3,5,19] (by decide +kernel)

private theorem m9_6 : availableMass (start .two6wide) ⟨31,3,0⟩ 65 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨31,3,0⟩ 65 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨31,3,0⟩ 65 248 [6,6,7,7,7,7,8,8,9,6,7,7,8,9,11,15,24,48,48] (by decide +kernel)

private theorem m9_7 : availableMass (start .two6wide) ⟨34,15,0⟩ 98 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨34,15,0⟩ 98 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨34,15,0⟩ 98 176 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,4,6,32] (by decide +kernel)

private theorem m9_8 : availableMass (start .two6wide) ⟨46,3,0⟩ 89 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨46,3,0⟩ 89 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨46,3,0⟩ 89 272 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,5,39,48,48] (by decide +kernel)

private theorem m9_9 : availableMass (start .two6wide) ⟨61,27,0⟩ 100 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨61,27,0⟩ 100 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨61,27,0⟩ 100 150 [1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,1,1,1,1,1,1,2,2,2,2,3,4,6,23] (by decide +kernel)

private theorem m9_10 : availableMass (start .two6wide) ⟨62,28,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨62,28,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨62,28,0⟩ 101 149 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,2,2,2,2,3,3,5,22] (by decide +kernel)

private theorem m9_11 : availableMass (start .two6wide) ⟨63,31,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨63,31,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨63,31,0⟩ 104 148 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,19] (by decide +kernel)

private theorem m9_12 : availableMass (start .two6wide) ⟨79,43,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨79,43,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨79,43,0⟩ 105 138 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,15] (by decide +kernel)

private theorem m9_13 : availableMass (start .two6wide) ⟨80,30,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨80,30,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨80,30,0⟩ 104 149 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,20] (by decide +kernel)

private theorem m9_14 : availableMass (start .two6wide) ⟨92,9,0⟩ 97 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,9,0⟩ 97 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨92,9,0⟩ 97 207 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,2,2,2,2,2,2,2,2,3,3,3,37,48] (by decide +kernel)

private theorem m9_15 : availableMass (start .two6wide) ⟨92,12,0⟩ 99 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,12,0⟩ 99 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨92,12,0⟩ 99 190 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,2,2,2,2,2,2,3,3,18,48] (by decide +kernel)

private theorem m9_16 : availableMass (start .two6wide) ⟨92,20,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,20,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨92,20,0⟩ 101 164 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,2,2,2,2,3,3,4,38] (by decide +kernel)

private theorem m9_17 : availableMass (start .two6wide) ⟨92,24,0⟩ 102 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,24,0⟩ 102 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨92,24,0⟩ 102 157 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,5,30] (by decide +kernel)

private theorem m9_18 : availableMass (start .two6wide) ⟨92,42,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,42,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨92,42,0⟩ 105 139 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,16] (by decide +kernel)

private theorem m9_19 : availableMass (start .two6wide) ⟨92,46,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨92,46,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨92,46,0⟩ 106 137 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m9_20 : availableMass (start .two6wide) ⟨100,41,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨100,41,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨100,41,0⟩ 105 140 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4,16] (by decide +kernel)

private theorem m9_21 : availableMass (start .two6wide) ⟨100,45,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨100,45,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨100,45,0⟩ 106 138 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m9_22 : availableMass (start .two6wide) ⟨104,44,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨104,44,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨104,44,0⟩ 106 139 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m9_23 : availableMass (start .two6wide) ⟨107,28,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨107,28,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨107,28,0⟩ 104 152 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,27] (by decide +kernel)

private theorem m9_24 : availableMass (start .two6wide) ⟨107,33,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨107,33,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨107,33,0⟩ 105 147 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4,21] (by decide +kernel)

private theorem m9_25 : availableMass (start .two6wide) ⟨111,43,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨111,43,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨111,43,0⟩ 106 139 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m9_26 : availableMass (start .two6wide) ⟨117,42,0⟩ 106 < layerNeed := by
  rw [mass_eq (start .two6wide) ⟨117,42,0⟩ 106 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wide) ⟨117,42,0⟩ 106 140 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_0 : availableMass (start .two6wider) ⟨1,3,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨1,3,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨1,3,0⟩ 72 255 [1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,4,4,4,4,5,5,6,7,9,11,21,48] (by decide +kernel)

private theorem m10_1 : availableMass (start .two6wider) ⟨4,12,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨4,12,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨4,12,0⟩ 90 181 [3,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,6,6,6,4,4,5,5,6,7,8,13,39] (by decide +kernel)

private theorem m10_2 : availableMass (start .two6wider) ⟨12,36,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨12,36,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨12,36,0⟩ 118 157 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,19] (by decide +kernel)

private theorem m10_3 : availableMass (start .two6wider) ⟨31,15,0⟩ 93 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨31,15,0⟩ 93 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨31,15,0⟩ 93 171 [4,4,4,5,5,5,5,5,5,6,6,6,6,6,7,7,7,4,4,5,6,8,12,39] (by decide +kernel)

private theorem m10_4 : availableMass (start .two6wider) ⟨32,6,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨32,6,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨32,6,0⟩ 96 233 [2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,3,3,3,3,4,4,4,5,6,7,11,36,48] (by decide +kernel)

private theorem m10_5 : availableMass (start .two6wider) ⟨35,27,0⟩ 101 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨35,27,0⟩ 101 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨35,27,0⟩ 101 151 [3,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,6,6,6,6,3,4,4,5,8,26] (by decide +kernel)

private theorem m10_6 : availableMass (start .two6wider) ⟨36,28,0⟩ 104 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨36,28,0⟩ 104 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨36,28,0⟩ 104 152 [3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,6,3,3,4,5,8,25] (by decide +kernel)

private theorem m10_7 : availableMass (start .two6wider) ⟨36,30,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨36,30,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨36,30,0⟩ 105 150 [3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,3,3,4,5,7,23] (by decide +kernel)

private theorem m10_8 : availableMass (start .two6wider) ⟨37,31,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨37,31,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨37,31,0⟩ 111 155 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,2,2,2,2,3,4,5,22] (by decide +kernel)

private theorem m10_9 : availableMass (start .two6wider) ⟨37,42,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨37,42,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨37,42,0⟩ 119 153 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,3,17] (by decide +kernel)

private theorem m10_10 : availableMass (start .two6wider) ⟨38,30,0⟩ 112 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨38,30,0⟩ 112 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨38,30,0⟩ 112 157 [1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,1,1,1,2,2,2,2,3,4,5,22] (by decide +kernel)

private theorem m10_11 : availableMass (start .two6wider) ⟨61,9,0⟩ 112 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨61,9,0⟩ 112 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨61,9,0⟩ 112 222 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,32,48] (by decide +kernel)

private theorem m10_12 : availableMass (start .two6wider) ⟨61,20,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨61,20,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨61,20,0⟩ 115 178 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,3,5,33] (by decide +kernel)

private theorem m10_13 : availableMass (start .two6wider) ⟨62,15,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨62,15,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨62,15,0⟩ 113 191 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,5,48] (by decide +kernel)

private theorem m10_14 : availableMass (start .two6wider) ⟨62,24,0⟩ 116 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨62,24,0⟩ 116 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨62,24,0⟩ 116 171 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,5,28] (by decide +kernel)

private theorem m10_15 : availableMass (start .two6wider) ⟨63,21,0⟩ 116 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨63,21,0⟩ 116 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨63,21,0⟩ 116 177 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,5,33] (by decide +kernel)

private theorem m10_16 : availableMass (start .two6wider) ⟨63,36,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨63,36,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨63,36,0⟩ 119 158 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_17 : availableMass (start .two6wider) ⟨69,49,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨69,49,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨69,49,0⟩ 120 150 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_18 : availableMass (start .two6wider) ⟨70,47,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨70,47,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨70,47,0⟩ 120 151 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_19 : availableMass (start .two6wider) ⟨74,46,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨74,46,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨74,46,0⟩ 120 151 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_20 : availableMass (start .two6wider) ⟨77,31,0⟩ 117 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨77,31,0⟩ 117 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨77,31,0⟩ 117 161 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,2,2,2,3,5,23] (by decide +kernel)

private theorem m10_21 : availableMass (start .two6wider) ⟨77,34,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨77,34,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨77,34,0⟩ 118 159 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,2,4,21] (by decide +kernel)

private theorem m10_22 : availableMass (start .two6wider) ⟨80,45,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨80,45,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨80,45,0⟩ 120 152 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_23 : availableMass (start .two6wider) ⟨83,35,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨83,35,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨83,35,0⟩ 119 159 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_24 : availableMass (start .two6wider) ⟨84,33,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨84,33,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨84,33,0⟩ 118 160 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,2,4,22] (by decide +kernel)

private theorem m10_25 : availableMass (start .two6wider) ⟨85,34,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨85,34,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨85,34,0⟩ 119 160 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_26 : availableMass (start .two6wider) ⟨87,44,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨87,44,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨87,44,0⟩ 120 153 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_27 : availableMass (start .two6wider) ⟨90,3,0⟩ 78 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨90,3,0⟩ 78 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨90,3,0⟩ 78 261 [9,10,10,11,12,12,14,10,11,18,48,48,48] (by decide +kernel)

private theorem m10_28 : availableMass (start .two6wider) ⟨90,31,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨90,31,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨90,31,0⟩ 118 162 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,2,4,24] (by decide +kernel)

private theorem m10_29 : availableMass (start .two6wider) ⟨91,26,0⟩ 117 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨91,26,0⟩ 117 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨91,26,0⟩ 117 168 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,30] (by decide +kernel)

private theorem m10_30 : availableMass (start .two6wider) ⟨91,29,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨91,29,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨91,29,0⟩ 118 165 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,3,4,26] (by decide +kernel)

private theorem m10_31 : availableMass (start .two6wider) ⟨93,43,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨93,43,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨93,43,0⟩ 120 153 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_32 : availableMass (start .two6wider) ⟨98,33,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨98,33,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨98,33,0⟩ 119 161 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,1,1,1,1,1,1,1,1,1,2,2,2,4,23] (by decide +kernel)

private theorem m10_33 : availableMass (start .two6wider) ⟨99,30,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨99,30,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨99,30,0⟩ 119 164 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_34 : availableMass (start .two6wider) ⟨100,42,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨100,42,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨100,42,0⟩ 120 154 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_35 : availableMass (start .two6wider) ⟨105,3,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,3,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨105,3,0⟩ 90 273 [6,6,6,7,7,7,7,8,8,9,9,10,6,6,7,20,48,48,48] (by decide +kernel)

private theorem m10_36 : availableMass (start .two6wider) ⟨105,20,0⟩ 117 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,20,0⟩ 117 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨105,20,0⟩ 117 180 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,45] (by decide +kernel)

private theorem m10_37 : availableMass (start .two6wider) ⟨105,25,0⟩ 118 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,25,0⟩ 118 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨105,25,0⟩ 118 171 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,2,2,3,35] (by decide +kernel)

private theorem m10_38 : availableMass (start .two6wider) ⟨105,29,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,29,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨105,29,0⟩ 119 166 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_39 : availableMass (start .two6wider) ⟨105,41,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨105,41,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨105,41,0⟩ 120 155 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_40 : availableMass (start .two6wider) ⟨107,28,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨107,28,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨107,28,0⟩ 119 167 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_41 : availableMass (start .two6wider) ⟨111,40,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨111,40,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨111,40,0⟩ 120 155 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_42 : availableMass (start .two6wider) ⟨114,26,0⟩ 119 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨114,26,0⟩ 119 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨114,26,0⟩ 119 170 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m10_43 : availableMass (start .two6wider) ⟨116,39,0⟩ 120 < layerNeed := by
  rw [mass_eq (start .two6wider) ⟨116,39,0⟩ 120 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two6wider) ⟨116,39,0⟩ 120 156 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m11_0 : availableMass (start .two7) ⟨1,3,0⟩ 39 < layerNeed := by
  rw [mass_eq (start .two7) ⟨1,3,0⟩ 39 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨1,3,0⟩ 39 204 [4,4,4,4,4,4,5,5,5,4,4,4,5,5,5,5,5,6,6,7,7,8,9,10,13,18,44] (by decide +kernel)

private theorem m11_1 : availableMass (start .two7) ⟨2,6,0⟩ 72 < layerNeed := by
  rw [mass_eq (start .two7) ⟨2,6,0⟩ 72 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨2,6,0⟩ 72 198 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m11_2 : availableMass (start .two7) ⟨5,15,0⟩ 83 < layerNeed := by
  rw [mass_eq (start .two7) ⟨5,15,0⟩ 83 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨5,15,0⟩ 83 158 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,2,2,2,2,2,2,2,3,3,3,4,4,5,8,31] (by decide +kernel)

private theorem m11_3 : availableMass (start .two7) ⟨9,26,0⟩ 86 < layerNeed := by
  rw [mass_eq (start .two7) ⟨9,26,0⟩ 86 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨9,26,0⟩ 86 136 [3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,5,2,3,3,3,4,5,7,23] (by decide +kernel)

private theorem m11_4 : availableMass (start .two7) ⟨10,29,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two7) ⟨10,29,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨10,29,0⟩ 90 135 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,1,2,2,2,2,2,2,3,4,5,20] (by decide +kernel)

private theorem m11_5 : availableMass (start .two7) ⟨34,3,0⟩ 59 < layerNeed := by
  rw [mass_eq (start .two7) ⟨34,3,0⟩ 59 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨34,3,0⟩ 59 224 [5,5,5,5,5,5,5,6,6,6,6,4,5,5,5,6,6,7,8,9,12,16,34,48] (by decide +kernel)

private theorem m11_6 : availableMass (start .two7) ⟨66,6,0⟩ 79 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,6,0⟩ 79 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨66,6,0⟩ 79 205 [2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,2,2,2,3,3,3,3,3,4,4,5,6,9,27,48] (by decide +kernel)

private theorem m11_7 : availableMass (start .two7) ⟨66,26,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two7) ⟨66,26,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨66,26,0⟩ 90 140 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,1,2,2,2,2,2,2,3,4,6,24] (by decide +kernel)

private theorem m11_8 : availableMass (start .two7) ⟨68,32,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two7) ⟨68,32,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨68,32,0⟩ 92 134 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,1,1,1,1,1,1,2,2,2,2,3,5,20] (by decide +kernel)

private theorem m11_9 : availableMass (start .two7) ⟨69,21,0⟩ 88 < layerNeed := by
  rw [mass_eq (start .two7) ⟨69,21,0⟩ 88 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨69,21,0⟩ 88 146 [2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,2,2,2,2,2,3,3,3,5,7,27] (by decide +kernel)

private theorem m11_10 : availableMass (start .two7) ⟨70,30,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7) ⟨70,30,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨70,30,0⟩ 94 138 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,20] (by decide +kernel)

private theorem m11_11 : availableMass (start .two7) ⟨85,27,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7) ⟨85,27,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨85,27,0⟩ 94 142 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,22] (by decide +kernel)

private theorem m11_12 : availableMass (start .two7) ⟨85,42,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .two7) ⟨85,42,0⟩ 95 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨85,42,0⟩ 95 128 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,3,16] (by decide +kernel)

private theorem m11_13 : availableMass (start .two7) ⟨86,45,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two7) ⟨86,45,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨86,45,0⟩ 96 127 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,3,14] (by decide +kernel)

private theorem m11_14 : availableMass (start .two7) ⟨98,15,0⟩ 88 < layerNeed := by
  rw [mass_eq (start .two7) ⟨98,15,0⟩ 88 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨98,15,0⟩ 88 163 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,3,1,2,2,2,2,2,2,3,3,4,5,7,40] (by decide +kernel)

private theorem m11_15 : availableMass (start .two7) ⟨98,17,0⟩ 92 < layerNeed := by
  rw [mass_eq (start .two7) ⟨98,17,0⟩ 92 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨98,17,0⟩ 92 160 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,3,5,33] (by decide +kernel)

private theorem m11_16 : availableMass (start .two7) ⟨98,39,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two7) ⟨98,39,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨98,39,0⟩ 96 131 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m11_17 : availableMass (start .two7) ⟨99,9,0⟩ 88 < layerNeed := by
  rw [mass_eq (start .two7) ⟨99,9,0⟩ 88 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨99,9,0⟩ 88 191 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,3,3,4,21,48] (by decide +kernel)

private theorem m11_18 : availableMass (start .two7) ⟨99,12,0⟩ 90 < layerNeed := by
  rw [mass_eq (start .two7) ⟨99,12,0⟩ 90 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨99,12,0⟩ 90 176 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,6,48] (by decide +kernel)

private theorem m11_19 : availableMass (start .two7) ⟨107,38,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .two7) ⟨107,38,0⟩ 95 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨107,38,0⟩ 95 131 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,2,2,4,17] (by decide +kernel)

private theorem m11_20 : availableMass (start .two7) ⟨115,31,0⟩ 95 < layerNeed := by
  rw [mass_eq (start .two7) ⟨115,31,0⟩ 95 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨115,31,0⟩ 95 138 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4,20] (by decide +kernel)

private theorem m11_21 : availableMass (start .two7) ⟨123,37,0⟩ 96 < layerNeed := by
  rw [mass_eq (start .two7) ⟨123,37,0⟩ 96 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7) ⟨123,37,0⟩ 96 133 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_0 : availableMass (start .two7wide) ⟨1,3,0⟩ 76 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨1,3,0⟩ 76 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨1,3,0⟩ 76 241 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,4,4,4,5,6,8,17,48] (by decide +kernel)

private theorem m12_1 : availableMass (start .two7wide) ⟨4,12,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨4,12,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨4,12,0⟩ 94 180 [2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,3,3,3,3,4,4,4,5,7,10,40] (by decide +kernel)

private theorem m12_2 : availableMass (start .two7wide) ⟨12,34,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨12,34,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨12,34,0⟩ 113 153 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,21] (by decide +kernel)

private theorem m12_3 : availableMass (start .two7wide) ⟨33,6,0⟩ 100 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨33,6,0⟩ 100 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨33,6,0⟩ 100 226 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,3,3,3,4,5,7,16,48] (by decide +kernel)

private theorem m12_4 : availableMass (start .two7wide) ⟨37,26,0⟩ 107 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨37,26,0⟩ 107 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨37,26,0⟩ 107 157 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,1,2,2,2,2,2,3,4,6,26] (by decide +kernel)

private theorem m12_5 : availableMass (start .two7wide) ⟨37,28,0⟩ 108 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨37,28,0⟩ 108 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨37,28,0⟩ 108 155 [1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,1,1,1,2,2,2,2,3,3,5,25] (by decide +kernel)

private theorem m12_6 : availableMass (start .two7wide) ⟨38,29,0⟩ 109 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨38,29,0⟩ 109 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨38,29,0⟩ 109 154 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,2,2,2,2,3,5,23] (by decide +kernel)

private theorem m12_7 : availableMass (start .two7wide) ⟨38,37,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨38,37,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨38,37,0⟩ 114 151 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,2,2,3,20] (by decide +kernel)

private theorem m12_8 : availableMass (start .two7wide) ⟨39,32,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨39,32,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨39,32,0⟩ 113 155 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,4,22] (by decide +kernel)

private theorem m12_9 : availableMass (start .two7wide) ⟨64,34,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨64,34,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨64,34,0⟩ 114 154 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,2,2,4,21] (by decide +kernel)

private theorem m12_10 : availableMass (start .two7wide) ⟨65,9,0⟩ 105 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨65,9,0⟩ 105 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨65,9,0⟩ 105 208 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,3,3,3,4,6,14,48] (by decide +kernel)

private theorem m12_11 : availableMass (start .two7wide) ⟨65,31,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨65,31,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨65,31,0⟩ 111 154 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,2,2,2,3,5,23] (by decide +kernel)

private theorem m12_12 : availableMass (start .two7wide) ⟨65,47,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨65,47,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨65,47,0⟩ 115 145 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,2,3,16] (by decide +kernel)

private theorem m12_13 : availableMass (start .two7wide) ⟨67,46,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨67,46,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨67,46,0⟩ 115 146 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,2,3,17] (by decide +kernel)

private theorem m12_14 : availableMass (start .two7wide) ⟨70,44,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨70,44,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨70,44,0⟩ 115 147 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,1,2,3,17] (by decide +kernel)

private theorem m12_15 : availableMass (start .two7wide) ⟨72,42,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨72,42,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨72,42,0⟩ 115 148 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_16 : availableMass (start .two7wide) ⟨80,23,0⟩ 107 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨80,23,0⟩ 107 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨80,23,0⟩ 107 162 [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,3,3,3,3,3,3,3,3,3,1,2,2,2,2,3,3,4,6,30] (by decide +kernel)

private theorem m12_17 : availableMass (start .two7wide) ⟨80,26,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨80,26,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨80,26,0⟩ 113 163 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,2,2,3,4,27] (by decide +kernel)

private theorem m12_18 : availableMass (start .two7wide) ⟨80,41,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨80,41,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨80,41,0⟩ 115 149 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_19 : availableMass (start .two7wide) ⟨81,24,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨81,24,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨81,24,0⟩ 111 164 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,3,5,29] (by decide +kernel)

private theorem m12_20 : availableMass (start .two7wide) ⟨82,21,0⟩ 112 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨82,21,0⟩ 112 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨82,21,0⟩ 112 170 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,5,31] (by decide +kernel)

private theorem m12_21 : availableMass (start .two7wide) ⟨84,33,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨84,33,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨84,33,0⟩ 114 155 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,2,2,4,22] (by decide +kernel)

private theorem m12_22 : availableMass (start .two7wide) ⟨88,32,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨88,32,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨88,32,0⟩ 114 156 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,2,2,4,23] (by decide +kernel)

private theorem m12_23 : availableMass (start .two7wide) ⟨89,31,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨89,31,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨89,31,0⟩ 114 157 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_24 : availableMass (start .two7wide) ⟨93,40,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨93,40,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨93,40,0⟩ 115 150 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_25 : availableMass (start .two7wide) ⟨95,3,0⟩ 82 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨95,3,0⟩ 82 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨95,3,0⟩ 82 247 [7,7,7,7,8,8,9,9,10,10,6,7,8,9,39,48,48] (by decide +kernel)

private theorem m12_26 : availableMass (start .two7wide) ⟨95,15,0⟩ 109 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨95,15,0⟩ 109 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨95,15,0⟩ 109 184 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,2,3,4,5,45] (by decide +kernel)

private theorem m12_27 : availableMass (start .two7wide) ⟨96,19,0⟩ 110 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨96,19,0⟩ 110 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨96,19,0⟩ 110 173 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,3,3,6,35] (by decide +kernel)

private theorem m12_28 : availableMass (start .two7wide) ⟨101,30,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨101,30,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨101,30,0⟩ 114 158 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_29 : availableMass (start .two7wide) ⟨106,39,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨106,39,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨106,39,0⟩ 115 150 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_30 : availableMass (start .two7wide) ⟨109,29,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨109,29,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨109,29,0⟩ 114 159 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_31 : availableMass (start .two7wide) ⟨111,3,0⟩ 94 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨111,3,0⟩ 94 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨111,3,0⟩ 94 259 [3,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,6,6,3,4,4,4,5,6,43,48,48] (by decide +kernel)

private theorem m12_32 : availableMass (start .two7wide) ⟨111,22,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨111,22,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨111,22,0⟩ 113 169 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_33 : availableMass (start .two7wide) ⟨118,38,0⟩ 115 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨118,38,0⟩ 115 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨118,38,0⟩ 115 151 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_34 : availableMass (start .two7wide) ⟨119,20,0⟩ 111 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨119,20,0⟩ 111 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨119,20,0⟩ 111 172 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2,3,5,37] (by decide +kernel)

private theorem m12_35 : availableMass (start .two7wide) ⟨119,21,0⟩ 113 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨119,21,0⟩ 113 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨119,21,0⟩ 113 171 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem m12_36 : availableMass (start .two7wide) ⟨120,28,0⟩ 114 < layerNeed := by
  rw [mass_eq (start .two7wide) ⟨120,28,0⟩ 114 (Or.inr (by decide)) (by decide)]
  exact mass_of_blocks (start .two7wide) ⟨120,28,0⟩ 114 161 [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (by decide +kernel)

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m0_0⟩
    · exact ⟨by decide, m0_1⟩
    · exact ⟨by decide, m0_2⟩
    · exact ⟨by decide, m0_3⟩
    · exact ⟨by decide, m0_4⟩
    · exact ⟨by decide, m0_5⟩
    · exact ⟨by decide, m0_6⟩
    · exact ⟨by decide, m0_7⟩
    · exact ⟨by decide, m0_8⟩
    · exact ⟨by decide, m0_9⟩
    · exact ⟨by decide, m0_10⟩
    · exact ⟨by decide, m0_11⟩
    · exact ⟨by decide, m0_12⟩
    · exact ⟨by decide, m0_13⟩
    · exact ⟨by decide, m0_14⟩
    · exact ⟨by decide, m0_15⟩
    · exact ⟨by decide, m0_16⟩
    · exact ⟨by decide, m0_17⟩
    · exact ⟨by decide, m0_18⟩
    · exact ⟨by decide, m0_19⟩
    · exact ⟨by decide, m0_20⟩
    · exact ⟨by decide, m0_21⟩
    · exact ⟨by decide, m0_22⟩
    · exact ⟨by decide, m0_23⟩
    · exact ⟨by decide, m0_24⟩
    · exact ⟨by decide, m0_25⟩
    · exact ⟨by decide, m0_26⟩
    · exact ⟨by decide, m0_27⟩
    · exact ⟨by decide, m0_28⟩
    · exact ⟨by decide, m0_29⟩
    · exact ⟨by decide, m0_30⟩
    · exact ⟨by decide, m0_31⟩
    · exact ⟨by decide, m0_32⟩
    · exact ⟨by decide, m0_33⟩
    · exact ⟨by decide, m0_34⟩
    · exact ⟨by decide, m0_35⟩
    · exact ⟨by decide, m0_36⟩
    · exact ⟨by decide, m0_37⟩
    · exact ⟨by decide, m0_38⟩
    · exact ⟨by decide, m0_39⟩
    · exact ⟨by decide, m0_40⟩
    · exact ⟨by decide, m0_41⟩
    · exact ⟨by decide, m0_42⟩
    · exact ⟨by decide, m0_43⟩
    · exact ⟨by decide, m0_44⟩
    · exact ⟨by decide, m0_45⟩
    · exact ⟨by decide, m0_46⟩
    · exact ⟨by decide, m0_47⟩
    · exact ⟨by decide, m0_48⟩
    · exact ⟨by decide, m0_49⟩
    · exact ⟨by decide, m0_50⟩
    · exact ⟨by decide, m0_51⟩
    · exact ⟨by decide, m0_52⟩
    · exact ⟨by decide, m0_53⟩
    · exact ⟨by decide, m0_54⟩
    · exact ⟨by decide, m0_55⟩
    · exact ⟨by decide, m0_56⟩
    · exact ⟨by decide, m0_57⟩
    · exact ⟨by decide, m0_58⟩
    · exact ⟨by decide, m0_59⟩
    · exact ⟨by decide, m0_60⟩
    · exact ⟨by decide, m0_61⟩
    · exact ⟨by decide, m0_62⟩
    · exact ⟨by decide, m0_63⟩
    · exact ⟨by decide, m0_64⟩
    · exact ⟨by decide, m0_65⟩
    · exact ⟨by decide, m0_66⟩
    · exact ⟨by decide, m0_67⟩
    · exact ⟨by decide, m0_68⟩
    · exact ⟨by decide, m0_69⟩
    · exact ⟨by decide, m0_70⟩
    · exact ⟨by decide, m0_71⟩
    · exact ⟨by decide, m0_72⟩
    · exact ⟨by decide, m0_73⟩
    · exact ⟨by decide, m0_74⟩
    · exact ⟨by decide, m0_75⟩
    · exact ⟨by decide, m0_76⟩
    · exact ⟨by decide, m0_77⟩
    · exact ⟨by decide, m0_78⟩
    · exact ⟨by decide, m0_79⟩
    · exact ⟨by decide, m0_80⟩
    · exact ⟨by decide, m0_81⟩
    · exact ⟨by decide, m0_82⟩
    · exact ⟨by decide, m0_83⟩
    · exact ⟨by decide, m0_84⟩
    · exact ⟨by decide, m0_85⟩
    · exact ⟨by decide, m0_86⟩
    · exact ⟨by decide, m0_87⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m1_0⟩
    · exact ⟨by decide, m1_1⟩
    · exact ⟨by decide, m1_2⟩
    · exact ⟨by decide, m1_3⟩
    · exact ⟨by decide, m1_4⟩
    · exact ⟨by decide, m1_5⟩
    · exact ⟨by decide, m1_6⟩
    · exact ⟨by decide, m1_7⟩
    · exact ⟨by decide, m1_8⟩
    · exact ⟨by decide, m1_9⟩
    · exact ⟨by decide, m1_10⟩
    · exact ⟨by decide, m1_11⟩
    · exact ⟨by decide, m1_12⟩
    · exact ⟨by decide, m1_13⟩
    · exact ⟨by decide, m1_14⟩
    · exact ⟨by decide, m1_15⟩
    · exact ⟨by decide, m1_16⟩
    · exact ⟨by decide, m1_17⟩
    · exact ⟨by decide, m1_18⟩
    · exact ⟨by decide, m1_19⟩
    · exact ⟨by decide, m1_20⟩
    · exact ⟨by decide, m1_21⟩
    · exact ⟨by decide, m1_22⟩
    · exact ⟨by decide, m1_23⟩
    · exact ⟨by decide, m1_24⟩
    · exact ⟨by decide, m1_25⟩
    · exact ⟨by decide, m1_26⟩
    · exact ⟨by decide, m1_27⟩
    · exact ⟨by decide, m1_28⟩
    · exact ⟨by decide, m1_29⟩
    · exact ⟨by decide, m1_30⟩
    · exact ⟨by decide, m1_31⟩
    · exact ⟨by decide, m1_32⟩
    · exact ⟨by decide, m1_33⟩
    · exact ⟨by decide, m1_34⟩
    · exact ⟨by decide, m1_35⟩
    · exact ⟨by decide, m1_36⟩
    · exact ⟨by decide, m1_37⟩
    · exact ⟨by decide, m1_38⟩
    · exact ⟨by decide, m1_39⟩
    · exact ⟨by decide, m1_40⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m2_0⟩
    · exact ⟨by decide, m2_1⟩
    · exact ⟨by decide, m2_2⟩
    · exact ⟨by decide, m2_3⟩
    · exact ⟨by decide, m2_4⟩
    · exact ⟨by decide, m2_5⟩
    · exact ⟨by decide, m2_6⟩
    · exact ⟨by decide, m2_7⟩
    · exact ⟨by decide, m2_8⟩
    · exact ⟨by decide, m2_9⟩
    · exact ⟨by decide, m2_10⟩
    · exact ⟨by decide, m2_11⟩
    · exact ⟨by decide, m2_12⟩
    · exact ⟨by decide, m2_13⟩
    · exact ⟨by decide, m2_14⟩
    · exact ⟨by decide, m2_15⟩
    · exact ⟨by decide, m2_16⟩
    · exact ⟨by decide, m2_17⟩
    · exact ⟨by decide, m2_18⟩
    · exact ⟨by decide, m2_19⟩
    · exact ⟨by decide, m2_20⟩
    · exact ⟨by decide, m2_21⟩
    · exact ⟨by decide, m2_22⟩
    · exact ⟨by decide, m2_23⟩
    · exact ⟨by decide, m2_24⟩
    · exact ⟨by decide, m2_25⟩
    · exact ⟨by decide, m2_26⟩
    · exact ⟨by decide, m2_27⟩
    · exact ⟨by decide, m2_28⟩
    · exact ⟨by decide, m2_29⟩
    · exact ⟨by decide, m2_30⟩
    · exact ⟨by decide, m2_31⟩
    · exact ⟨by decide, m2_32⟩
    · exact ⟨by decide, m2_33⟩
    · exact ⟨by decide, m2_34⟩
    · exact ⟨by decide, m2_35⟩
    · exact ⟨by decide, m2_36⟩
    · exact ⟨by decide, m2_37⟩
    · exact ⟨by decide, m2_38⟩
    · exact ⟨by decide, m2_39⟩
    · exact ⟨by decide, m2_40⟩
    · exact ⟨by decide, m2_41⟩
    · exact ⟨by decide, m2_42⟩
    · exact ⟨by decide, m2_43⟩
    · exact ⟨by decide, m2_44⟩
    · exact ⟨by decide, m2_45⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m3_0⟩
    · exact ⟨by decide, m3_1⟩
    · exact ⟨by decide, m3_2⟩
    · exact ⟨by decide, m3_3⟩
    · exact ⟨by decide, m3_4⟩
    · exact ⟨by decide, m3_5⟩
    · exact ⟨by decide, m3_6⟩
    · exact ⟨by decide, m3_7⟩
    · exact ⟨by decide, m3_8⟩
    · exact ⟨by decide, m3_9⟩
    · exact ⟨by decide, m3_10⟩
    · exact ⟨by decide, m3_11⟩
    · exact ⟨by decide, m3_12⟩
    · exact ⟨by decide, m3_13⟩
    · exact ⟨by decide, m3_14⟩
    · exact ⟨by decide, m3_15⟩
    · exact ⟨by decide, m3_16⟩
    · exact ⟨by decide, m3_17⟩
    · exact ⟨by decide, m3_18⟩
    · exact ⟨by decide, m3_19⟩
    · exact ⟨by decide, m3_20⟩
    · exact ⟨by decide, m3_21⟩
    · exact ⟨by decide, m3_22⟩
    · exact ⟨by decide, m3_23⟩
    · exact ⟨by decide, m3_24⟩
    · exact ⟨by decide, m3_25⟩
    · exact ⟨by decide, m3_26⟩
    · exact ⟨by decide, m3_27⟩
    · exact ⟨by decide, m3_28⟩
    · exact ⟨by decide, m3_29⟩
    · exact ⟨by decide, m3_30⟩
    · exact ⟨by decide, m3_31⟩
    · exact ⟨by decide, m3_32⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m4_0⟩
    · exact ⟨by decide, m4_1⟩
    · exact ⟨by decide, m4_2⟩
    · exact ⟨by decide, m4_3⟩
    · exact ⟨by decide, m4_4⟩
    · exact ⟨by decide, m4_5⟩
    · exact ⟨by decide, m4_6⟩
    · exact ⟨by decide, m4_7⟩
    · exact ⟨by decide, m4_8⟩
    · exact ⟨by decide, m4_9⟩
    · exact ⟨by decide, m4_10⟩
    · exact ⟨by decide, m4_11⟩
    · exact ⟨by decide, m4_12⟩
    · exact ⟨by decide, m4_13⟩
    · exact ⟨by decide, m4_14⟩
    · exact ⟨by decide, m4_15⟩
    · exact ⟨by decide, m4_16⟩
    · exact ⟨by decide, m4_17⟩
    · exact ⟨by decide, m4_18⟩
    · exact ⟨by decide, m4_19⟩
    · exact ⟨by decide, m4_20⟩
    · exact ⟨by decide, m4_21⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m5_0⟩
    · exact ⟨by decide, m5_1⟩
    · exact ⟨by decide, m5_2⟩
    · exact ⟨by decide, m5_3⟩
    · exact ⟨by decide, m5_4⟩
    · exact ⟨by decide, m5_5⟩
    · exact ⟨by decide, m5_6⟩
    · exact ⟨by decide, m5_7⟩
    · exact ⟨by decide, m5_8⟩
    · exact ⟨by decide, m5_9⟩
    · exact ⟨by decide, m5_10⟩
    · exact ⟨by decide, m5_11⟩
    · exact ⟨by decide, m5_12⟩
    · exact ⟨by decide, m5_13⟩
    · exact ⟨by decide, m5_14⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m6_0⟩
    · exact ⟨by decide, m6_1⟩
    · exact ⟨by decide, m6_2⟩
    · exact ⟨by decide, m6_3⟩
    · exact ⟨by decide, m6_4⟩
    · exact ⟨by decide, m6_5⟩
    · exact ⟨by decide, m6_6⟩
    · exact ⟨by decide, m6_7⟩
    · exact ⟨by decide, m6_8⟩
    · exact ⟨by decide, m6_9⟩
    · exact ⟨by decide, m6_10⟩
    · exact ⟨by decide, m6_11⟩
    · exact ⟨by decide, m6_12⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m7_0⟩
    · exact ⟨by decide, m7_1⟩
    · exact ⟨by decide, m7_2⟩
    · exact ⟨by decide, m7_3⟩
    · exact ⟨by decide, m7_4⟩
    · exact ⟨by decide, m7_5⟩
    · exact ⟨by decide, m7_6⟩
    · exact ⟨by decide, m7_7⟩
    · exact ⟨by decide, m7_8⟩
    · exact ⟨by decide, m7_9⟩
    · exact ⟨by decide, m7_10⟩
    · exact ⟨by decide, m7_11⟩
    · exact ⟨by decide, m7_12⟩
    · exact ⟨by decide, m7_13⟩
    · exact ⟨by decide, m7_14⟩
    · exact ⟨by decide, m7_15⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m8_0⟩
    · exact ⟨by decide, m8_1⟩
    · exact ⟨by decide, m8_2⟩
    · exact ⟨by decide, m8_3⟩
    · exact ⟨by decide, m8_4⟩
    · exact ⟨by decide, m8_5⟩
    · exact ⟨by decide, m8_6⟩
    · exact ⟨by decide, m8_7⟩
    · exact ⟨by decide, m8_8⟩
    · exact ⟨by decide, m8_9⟩
    · exact ⟨by decide, m8_10⟩
    · exact ⟨by decide, m8_11⟩
    · exact ⟨by decide, m8_12⟩
    · exact ⟨by decide, m8_13⟩
    · exact ⟨by decide, m8_14⟩
    · exact ⟨by decide, m8_15⟩
    · exact ⟨by decide, m8_16⟩
    · exact ⟨by decide, m8_17⟩
    · exact ⟨by decide, m8_18⟩
    · exact ⟨by decide, m8_19⟩
    · exact ⟨by decide, m8_20⟩
    · exact ⟨by decide, m8_21⟩
    · exact ⟨by decide, m8_22⟩
    · exact ⟨by decide, m8_23⟩
    · exact ⟨by decide, m8_24⟩
    · exact ⟨by decide, m8_25⟩
    · exact ⟨by decide, m8_26⟩
    · exact ⟨by decide, m8_27⟩
    · exact ⟨by decide, m8_28⟩
    · exact ⟨by decide, m8_29⟩
    · exact ⟨by decide, m8_30⟩
    · exact ⟨by decide, m8_31⟩
    · exact ⟨by decide, m8_32⟩
    · exact ⟨by decide, m8_33⟩
    · exact ⟨by decide, m8_34⟩
    · exact ⟨by decide, m8_35⟩
    · exact ⟨by decide, m8_36⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m9_0⟩
    · exact ⟨by decide, m9_1⟩
    · exact ⟨by decide, m9_2⟩
    · exact ⟨by decide, m9_3⟩
    · exact ⟨by decide, m9_4⟩
    · exact ⟨by decide, m9_5⟩
    · exact ⟨by decide, m9_6⟩
    · exact ⟨by decide, m9_7⟩
    · exact ⟨by decide, m9_8⟩
    · exact ⟨by decide, m9_9⟩
    · exact ⟨by decide, m9_10⟩
    · exact ⟨by decide, m9_11⟩
    · exact ⟨by decide, m9_12⟩
    · exact ⟨by decide, m9_13⟩
    · exact ⟨by decide, m9_14⟩
    · exact ⟨by decide, m9_15⟩
    · exact ⟨by decide, m9_16⟩
    · exact ⟨by decide, m9_17⟩
    · exact ⟨by decide, m9_18⟩
    · exact ⟨by decide, m9_19⟩
    · exact ⟨by decide, m9_20⟩
    · exact ⟨by decide, m9_21⟩
    · exact ⟨by decide, m9_22⟩
    · exact ⟨by decide, m9_23⟩
    · exact ⟨by decide, m9_24⟩
    · exact ⟨by decide, m9_25⟩
    · exact ⟨by decide, m9_26⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m10_0⟩
    · exact ⟨by decide, m10_1⟩
    · exact ⟨by decide, m10_2⟩
    · exact ⟨by decide, m10_3⟩
    · exact ⟨by decide, m10_4⟩
    · exact ⟨by decide, m10_5⟩
    · exact ⟨by decide, m10_6⟩
    · exact ⟨by decide, m10_7⟩
    · exact ⟨by decide, m10_8⟩
    · exact ⟨by decide, m10_9⟩
    · exact ⟨by decide, m10_10⟩
    · exact ⟨by decide, m10_11⟩
    · exact ⟨by decide, m10_12⟩
    · exact ⟨by decide, m10_13⟩
    · exact ⟨by decide, m10_14⟩
    · exact ⟨by decide, m10_15⟩
    · exact ⟨by decide, m10_16⟩
    · exact ⟨by decide, m10_17⟩
    · exact ⟨by decide, m10_18⟩
    · exact ⟨by decide, m10_19⟩
    · exact ⟨by decide, m10_20⟩
    · exact ⟨by decide, m10_21⟩
    · exact ⟨by decide, m10_22⟩
    · exact ⟨by decide, m10_23⟩
    · exact ⟨by decide, m10_24⟩
    · exact ⟨by decide, m10_25⟩
    · exact ⟨by decide, m10_26⟩
    · exact ⟨by decide, m10_27⟩
    · exact ⟨by decide, m10_28⟩
    · exact ⟨by decide, m10_29⟩
    · exact ⟨by decide, m10_30⟩
    · exact ⟨by decide, m10_31⟩
    · exact ⟨by decide, m10_32⟩
    · exact ⟨by decide, m10_33⟩
    · exact ⟨by decide, m10_34⟩
    · exact ⟨by decide, m10_35⟩
    · exact ⟨by decide, m10_36⟩
    · exact ⟨by decide, m10_37⟩
    · exact ⟨by decide, m10_38⟩
    · exact ⟨by decide, m10_39⟩
    · exact ⟨by decide, m10_40⟩
    · exact ⟨by decide, m10_41⟩
    · exact ⟨by decide, m10_42⟩
    · exact ⟨by decide, m10_43⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m11_0⟩
    · exact ⟨by decide, m11_1⟩
    · exact ⟨by decide, m11_2⟩
    · exact ⟨by decide, m11_3⟩
    · exact ⟨by decide, m11_4⟩
    · exact ⟨by decide, m11_5⟩
    · exact ⟨by decide, m11_6⟩
    · exact ⟨by decide, m11_7⟩
    · exact ⟨by decide, m11_8⟩
    · exact ⟨by decide, m11_9⟩
    · exact ⟨by decide, m11_10⟩
    · exact ⟨by decide, m11_11⟩
    · exact ⟨by decide, m11_12⟩
    · exact ⟨by decide, m11_13⟩
    · exact ⟨by decide, m11_14⟩
    · exact ⟨by decide, m11_15⟩
    · exact ⟨by decide, m11_16⟩
    · exact ⟨by decide, m11_17⟩
    · exact ⟨by decide, m11_18⟩
    · exact ⟨by decide, m11_19⟩
    · exact ⟨by decide, m11_20⟩
    · exact ⟨by decide, m11_21⟩
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, m12_0⟩
    · exact ⟨by decide, m12_1⟩
    · exact ⟨by decide, m12_2⟩
    · exact ⟨by decide, m12_3⟩
    · exact ⟨by decide, m12_4⟩
    · exact ⟨by decide, m12_5⟩
    · exact ⟨by decide, m12_6⟩
    · exact ⟨by decide, m12_7⟩
    · exact ⟨by decide, m12_8⟩
    · exact ⟨by decide, m12_9⟩
    · exact ⟨by decide, m12_10⟩
    · exact ⟨by decide, m12_11⟩
    · exact ⟨by decide, m12_12⟩
    · exact ⟨by decide, m12_13⟩
    · exact ⟨by decide, m12_14⟩
    · exact ⟨by decide, m12_15⟩
    · exact ⟨by decide, m12_16⟩
    · exact ⟨by decide, m12_17⟩
    · exact ⟨by decide, m12_18⟩
    · exact ⟨by decide, m12_19⟩
    · exact ⟨by decide, m12_20⟩
    · exact ⟨by decide, m12_21⟩
    · exact ⟨by decide, m12_22⟩
    · exact ⟨by decide, m12_23⟩
    · exact ⟨by decide, m12_24⟩
    · exact ⟨by decide, m12_25⟩
    · exact ⟨by decide, m12_26⟩
    · exact ⟨by decide, m12_27⟩
    · exact ⟨by decide, m12_28⟩
    · exact ⟨by decide, m12_29⟩
    · exact ⟨by decide, m12_30⟩
    · exact ⟨by decide, m12_31⟩
    · exact ⟨by decide, m12_32⟩
    · exact ⟨by decide, m12_33⟩
    · exact ⟨by decide, m12_34⟩
    · exact ⟨by decide, m12_35⟩
    · exact ⟨by decide, m12_36⟩

theorem order_valid (k : Band) (x : Shape) : order k x = 1 ∨
    availableMass (start k) x (order k x - 1) < layerNeed := by
  rcases (P0_9_8.orderFor_select x.b x.j (thresholds k)).2 with h | ⟨q,hq,hb,hj,he⟩
  · exact Or.inl h
  · right
    change order k x = q.l at he
    rw [he]
    obtain ⟨hpos, hsmall⟩ := thresholds_valid k q hq
    have hr : start k = zeroShape ∨ 0 < (start k).j := by cases k <;> decide
    have hi : 0 < (start k).j + q.j := by omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end Final50PriceMass
