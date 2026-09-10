import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r25_part16 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 16 := by decide +kernel
  exact zeroAtFast_sound 25 16 hfast

theorem zero_r25_part17 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 17 := by decide +kernel
  exact zeroAtFast_sound 25 17 hfast

theorem zero_r25_part18 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 18 := by decide +kernel
  exact zeroAtFast_sound 25 18 hfast

theorem zero_r25_part19 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 19 := by decide +kernel
  exact zeroAtFast_sound 25 19 hfast

theorem zero_r25_part20 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 20 := by decide +kernel
  exact zeroAtFast_sound 25 20 hfast

theorem zero_r25_part21 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 21 := by decide +kernel
  exact zeroAtFast_sound 25 21 hfast

theorem zero_r25_part22 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 22 := by decide +kernel
  exact zeroAtFast_sound 25 22 hfast

theorem zero_r25_part23 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 23 := by decide +kernel
  exact zeroAtFast_sound 25 23 hfast

theorem zero_r25_part24 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 24 := by decide +kernel
  exact zeroAtFast_sound 25 24 hfast

theorem zero_r25_part25 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 25 := by decide +kernel
  exact zeroAtFast_sound 25 25 hfast

theorem zero_r25_part26 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 26 := by decide +kernel
  exact zeroAtFast_sound 25 26 hfast

theorem zero_r25_part27 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 27 := by decide +kernel
  exact zeroAtFast_sound 25 27 hfast

theorem zero_r25_part28 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 28 := by decide +kernel
  exact zeroAtFast_sound 25 28 hfast

theorem zero_r25_part29 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 29 := by decide +kernel
  exact zeroAtFast_sound 25 29 hfast

theorem zero_r25_part30 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 30 := by decide +kernel
  exact zeroAtFast_sound 25 30 hfast

theorem zero_r25_part31 : ∀ i ∈ List.range 1, ZeroCheckAt 25 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 25 31 := by decide +kernel
  exact zeroAtFast_sound 25 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
