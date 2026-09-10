import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r28_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 0 := by decide +kernel
  exact zeroAtFast_sound 28 0 hfast

theorem zero_r28_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 1 := by decide +kernel
  exact zeroAtFast_sound 28 1 hfast

theorem zero_r28_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 2 := by decide +kernel
  exact zeroAtFast_sound 28 2 hfast

theorem zero_r28_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 3 := by decide +kernel
  exact zeroAtFast_sound 28 3 hfast

theorem zero_r28_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 4 := by decide +kernel
  exact zeroAtFast_sound 28 4 hfast

theorem zero_r28_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 5 := by decide +kernel
  exact zeroAtFast_sound 28 5 hfast

theorem zero_r28_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 6 := by decide +kernel
  exact zeroAtFast_sound 28 6 hfast

theorem zero_r28_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 7 := by decide +kernel
  exact zeroAtFast_sound 28 7 hfast

theorem zero_r28_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 8 := by decide +kernel
  exact zeroAtFast_sound 28 8 hfast

theorem zero_r28_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 9 := by decide +kernel
  exact zeroAtFast_sound 28 9 hfast

theorem zero_r28_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 10 := by decide +kernel
  exact zeroAtFast_sound 28 10 hfast

theorem zero_r28_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 11 := by decide +kernel
  exact zeroAtFast_sound 28 11 hfast

theorem zero_r28_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 12 := by decide +kernel
  exact zeroAtFast_sound 28 12 hfast

theorem zero_r28_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 13 := by decide +kernel
  exact zeroAtFast_sound 28 13 hfast

theorem zero_r28_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 14 := by decide +kernel
  exact zeroAtFast_sound 28 14 hfast

theorem zero_r28_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 28 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 28 15 := by decide +kernel
  exact zeroAtFast_sound 28 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
