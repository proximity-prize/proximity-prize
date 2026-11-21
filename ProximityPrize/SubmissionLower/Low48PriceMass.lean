import ProximityPrize.SubmissionLower.Low48PriceCaps

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
namespace Low48PriceMass
open Low48PriceCaps (Band start thresholds order)
open Low48Price (layerNeed)
open K1_13 (Shape remaining)
open K1_13_8 (availableMass layerTerm zeroShape fastRemaining)
open K1_13_8_2 (Threshold)
open P0_9_8 (symbol_count)
open private P3_6_8_1.sumBelow P3_6_8_1.sumBelow_eq P3_6_8_1.extend
  from ProximityPrize.SubmissionLower.GoldBranch6N8

private def fastLayer (r y : Shape) (L i : ℕ) :=
  fastRemaining ((i+1)*r.b + (i+1-L)*y.b) ((i+1)*r.j + (i+1-L)*y.j)
private theorem mass_eq (r y : Shape) (L : ℕ) (hr : r = zeroShape ∨ 0 < r.j)
    (hj : 0 < r.j+y.j) : availableMass r y L =
    P3_6_8_1.sumBelow (fastLayer r y L) (L + 1650 / (r.j+y.j)) := by
  rw [P3_6_8_1.sumBelow_eq, ← K1_13_8.availableMass_eq_sum symbol_count hr hj le_rfl]
  simp only [layerTerm, fastLayer, symbol_count]

private theorem m0_0 : availableMass (start .empty) (⟨1,9,0⟩ : Shape) 9 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,9,0⟩ : Shape) 9 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_1 : availableMass (start .empty) (⟨1,10,0⟩ : Shape) 13 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,10,0⟩ : Shape) 13 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_2 : availableMass (start .empty) (⟨1,11,0⟩ : Shape) 17 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,11,0⟩ : Shape) 17 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_3 : availableMass (start .empty) (⟨1,12,0⟩ : Shape) 20 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,12,0⟩ : Shape) 20 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_4 : availableMass (start .empty) (⟨1,13,0⟩ : Shape) 23 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,13,0⟩ : Shape) 23 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_5 : availableMass (start .empty) (⟨1,14,0⟩ : Shape) 25 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,14,0⟩ : Shape) 25 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_6 : availableMass (start .empty) (⟨1,15,0⟩ : Shape) 28 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,15,0⟩ : Shape) 28 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_7 : availableMass (start .empty) (⟨1,16,0⟩ : Shape) 29 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,16,0⟩ : Shape) 29 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_8 : availableMass (start .empty) (⟨1,17,0⟩ : Shape) 31 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,17,0⟩ : Shape) 31 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_9 : availableMass (start .empty) (⟨1,18,0⟩ : Shape) 32 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,18,0⟩ : Shape) 32 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_10 : availableMass (start .empty) (⟨1,19,0⟩ : Shape) 34 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,19,0⟩ : Shape) 34 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_11 : availableMass (start .empty) (⟨1,20,0⟩ : Shape) 35 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,20,0⟩ : Shape) 35 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_12 : availableMass (start .empty) (⟨1,21,0⟩ : Shape) 36 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,21,0⟩ : Shape) 36 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_13 : availableMass (start .empty) (⟨1,22,0⟩ : Shape) 37 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,22,0⟩ : Shape) 37 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_14 : availableMass (start .empty) (⟨1,24,0⟩ : Shape) 38 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,24,0⟩ : Shape) 38 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_15 : availableMass (start .empty) (⟨1,25,0⟩ : Shape) 39 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,25,0⟩ : Shape) 39 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_16 : availableMass (start .empty) (⟨1,26,0⟩ : Shape) 40 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,26,0⟩ : Shape) 40 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_17 : availableMass (start .empty) (⟨1,28,0⟩ : Shape) 41 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,28,0⟩ : Shape) 41 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_18 : availableMass (start .empty) (⟨1,30,0⟩ : Shape) 42 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,30,0⟩ : Shape) 42 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_19 : availableMass (start .empty) (⟨1,32,0⟩ : Shape) 43 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,32,0⟩ : Shape) 43 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_20 : availableMass (start .empty) (⟨1,35,0⟩ : Shape) 44 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,35,0⟩ : Shape) 44 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_21 : availableMass (start .empty) (⟨1,37,0⟩ : Shape) 45 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,37,0⟩ : Shape) 45 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_22 : availableMass (start .empty) (⟨1,41,0⟩ : Shape) 46 < layerNeed := by
  rw [mass_eq (start .empty) (⟨1,41,0⟩ : Shape) 46 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_23 : availableMass (start .empty) (⟨6,8,0⟩ : Shape) 6 < layerNeed := by
  rw [mass_eq (start .empty) (⟨6,8,0⟩ : Shape) 6 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_24 : availableMass (start .empty) (⟨7,8,0⟩ : Shape) 7 < layerNeed := by
  rw [mass_eq (start .empty) (⟨7,8,0⟩ : Shape) 7 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_25 : availableMass (start .empty) (⟨8,44,0⟩ : Shape) 47 < layerNeed := by
  rw [mass_eq (start .empty) (⟨8,44,0⟩ : Shape) 47 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_26 : availableMass (start .empty) (⟨12,7,0⟩ : Shape) 5 < layerNeed := by
  rw [mass_eq (start .empty) (⟨12,7,0⟩ : Shape) 5 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_27 : availableMass (start .empty) (⟨17,6,0⟩ : Shape) 4 < layerNeed := by
  rw [mass_eq (start .empty) (⟨17,6,0⟩ : Shape) 4 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_28 : availableMass (start .empty) (⟨20,5,0⟩ : Shape) 3 < layerNeed := by
  rw [mass_eq (start .empty) (⟨20,5,0⟩ : Shape) 3 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_29 : availableMass (start .empty) (⟨22,4,0⟩ : Shape) 1 < layerNeed := by
  rw [mass_eq (start .empty) (⟨22,4,0⟩ : Shape) 1 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_30 : availableMass (start .empty) (⟨46,45,0⟩ : Shape) 48 < layerNeed := by
  rw [mass_eq (start .empty) (⟨46,45,0⟩ : Shape) 48 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_31 : availableMass (start .empty) (⟨88,46,0⟩ : Shape) 49 < layerNeed := by
  rw [mass_eq (start .empty) (⟨88,46,0⟩ : Shape) 49 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m0_32 : availableMass (start .empty) (⟨119,50,0⟩ : Shape) 50 < layerNeed := by
  rw [mass_eq (start .empty) (⟨119,50,0⟩ : Shape) 50 (Or.inl rfl) (by decide)]
  decide +kernel

private theorem m1_0 : availableMass (start .one) (⟨1,5,0⟩ : Shape) 6 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,5,0⟩ : Shape) 6 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_1 : availableMass (start .one) (⟨1,6,0⟩ : Shape) 15 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,6,0⟩ : Shape) 15 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_2 : availableMass (start .one) (⟨1,7,0⟩ : Shape) 21 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,7,0⟩ : Shape) 21 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_3 : availableMass (start .one) (⟨1,8,0⟩ : Shape) 26 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,8,0⟩ : Shape) 26 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_4 : availableMass (start .one) (⟨1,9,0⟩ : Shape) 30 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,9,0⟩ : Shape) 30 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_5 : availableMass (start .one) (⟨1,10,0⟩ : Shape) 34 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,10,0⟩ : Shape) 34 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_6 : availableMass (start .one) (⟨1,11,0⟩ : Shape) 37 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,11,0⟩ : Shape) 37 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_7 : availableMass (start .one) (⟨1,12,0⟩ : Shape) 39 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,12,0⟩ : Shape) 39 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_8 : availableMass (start .one) (⟨1,13,0⟩ : Shape) 41 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,13,0⟩ : Shape) 41 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_9 : availableMass (start .one) (⟨1,14,0⟩ : Shape) 43 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,14,0⟩ : Shape) 43 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_10 : availableMass (start .one) (⟨1,15,0⟩ : Shape) 44 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,15,0⟩ : Shape) 44 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_11 : availableMass (start .one) (⟨1,16,0⟩ : Shape) 46 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,16,0⟩ : Shape) 46 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_12 : availableMass (start .one) (⟨1,17,0⟩ : Shape) 47 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,17,0⟩ : Shape) 47 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_13 : availableMass (start .one) (⟨1,18,0⟩ : Shape) 48 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,18,0⟩ : Shape) 48 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_14 : availableMass (start .one) (⟨1,19,0⟩ : Shape) 49 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,19,0⟩ : Shape) 49 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_15 : availableMass (start .one) (⟨1,20,0⟩ : Shape) 50 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,20,0⟩ : Shape) 50 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_16 : availableMass (start .one) (⟨1,21,0⟩ : Shape) 51 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,21,0⟩ : Shape) 51 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_17 : availableMass (start .one) (⟨1,23,0⟩ : Shape) 52 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,23,0⟩ : Shape) 52 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_18 : availableMass (start .one) (⟨1,24,0⟩ : Shape) 53 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,24,0⟩ : Shape) 53 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_19 : availableMass (start .one) (⟨1,26,0⟩ : Shape) 54 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,26,0⟩ : Shape) 54 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_20 : availableMass (start .one) (⟨1,28,0⟩ : Shape) 55 < layerNeed := by
  rw [mass_eq (start .one) (⟨1,28,0⟩ : Shape) 55 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m1_21 : availableMass (start .one) (⟨6,4,0⟩ : Shape) 1 < layerNeed := by
  rw [mass_eq (start .one) (⟨6,4,0⟩ : Shape) 1 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_0 : availableMass (start .two) (⟨1,2,0⟩ : Shape) 20 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,2,0⟩ : Shape) 20 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_1 : availableMass (start .two) (⟨1,3,0⟩ : Shape) 37 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,3,0⟩ : Shape) 37 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_2 : availableMass (start .two) (⟨1,4,0⟩ : Shape) 47 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,4,0⟩ : Shape) 47 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_3 : availableMass (start .two) (⟨1,5,0⟩ : Shape) 54 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,5,0⟩ : Shape) 54 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_4 : availableMass (start .two) (⟨1,6,0⟩ : Shape) 60 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,6,0⟩ : Shape) 60 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_5 : availableMass (start .two) (⟨1,7,0⟩ : Shape) 64 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,7,0⟩ : Shape) 64 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_6 : availableMass (start .two) (⟨1,8,0⟩ : Shape) 67 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,8,0⟩ : Shape) 67 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_7 : availableMass (start .two) (⟨1,9,0⟩ : Shape) 69 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,9,0⟩ : Shape) 69 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_8 : availableMass (start .two) (⟨1,10,0⟩ : Shape) 71 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,10,0⟩ : Shape) 71 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_9 : availableMass (start .two) (⟨1,11,0⟩ : Shape) 73 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,11,0⟩ : Shape) 73 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_10 : availableMass (start .two) (⟨1,12,0⟩ : Shape) 75 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,12,0⟩ : Shape) 75 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_11 : availableMass (start .two) (⟨1,13,0⟩ : Shape) 76 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,13,0⟩ : Shape) 76 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_12 : availableMass (start .two) (⟨1,14,0⟩ : Shape) 77 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,14,0⟩ : Shape) 77 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_13 : availableMass (start .two) (⟨1,15,0⟩ : Shape) 78 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,15,0⟩ : Shape) 78 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_14 : availableMass (start .two) (⟨1,16,0⟩ : Shape) 79 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,16,0⟩ : Shape) 79 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_15 : availableMass (start .two) (⟨1,17,0⟩ : Shape) 80 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,17,0⟩ : Shape) 80 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_16 : availableMass (start .two) (⟨1,18,0⟩ : Shape) 81 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,18,0⟩ : Shape) 81 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_17 : availableMass (start .two) (⟨1,20,0⟩ : Shape) 82 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,20,0⟩ : Shape) 82 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_18 : availableMass (start .two) (⟨1,22,0⟩ : Shape) 83 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,22,0⟩ : Shape) 83 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_19 : availableMass (start .two) (⟨1,24,0⟩ : Shape) 84 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,24,0⟩ : Shape) 84 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_20 : availableMass (start .two) (⟨1,26,0⟩ : Shape) 85 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,26,0⟩ : Shape) 85 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_21 : availableMass (start .two) (⟨1,29,0⟩ : Shape) 86 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,29,0⟩ : Shape) 86 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_22 : availableMass (start .two) (⟨1,33,0⟩ : Shape) 87 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,33,0⟩ : Shape) 87 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem m2_23 : availableMass (start .two) (⟨1,38,0⟩ : Shape) 88 < layerNeed := by
  rw [mass_eq (start .two) (⟨1,38,0⟩ : Shape) 88 (Or.inr (by decide)) (by decide)]
  decide +kernel

private theorem thresholds_valid (k : Band) (q : Threshold) (hq : q ∈ thresholds k) :
    0 < q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1) < layerNeed := by
  cases k
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · simp only [thresholds, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
    exact (P0_9_8.availableMass_anti_prefix (y := ⟨q.b,q.j,0⟩) hr hi hb hj).trans_lt hsmall
#print axioms order_valid
end Low48PriceMass
