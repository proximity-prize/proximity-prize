import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r26_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 0 := by decide +kernel
  exact zeroAtFast_sound 26 0 hfast

theorem zero_r26_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 1 := by decide +kernel
  exact zeroAtFast_sound 26 1 hfast

theorem zero_r26_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 2 := by decide +kernel
  exact zeroAtFast_sound 26 2 hfast

theorem zero_r26_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 3 := by decide +kernel
  exact zeroAtFast_sound 26 3 hfast

theorem zero_r26_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 4 := by decide +kernel
  exact zeroAtFast_sound 26 4 hfast

theorem zero_r26_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 5 := by decide +kernel
  exact zeroAtFast_sound 26 5 hfast

theorem zero_r26_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 6 := by decide +kernel
  exact zeroAtFast_sound 26 6 hfast

theorem zero_r26_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 7 := by decide +kernel
  exact zeroAtFast_sound 26 7 hfast

theorem zero_r26_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 8 := by decide +kernel
  exact zeroAtFast_sound 26 8 hfast

theorem zero_r26_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 9 := by decide +kernel
  exact zeroAtFast_sound 26 9 hfast

theorem zero_r26_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 10 := by decide +kernel
  exact zeroAtFast_sound 26 10 hfast

theorem zero_r26_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 11 := by decide +kernel
  exact zeroAtFast_sound 26 11 hfast

theorem zero_r26_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 12 := by decide +kernel
  exact zeroAtFast_sound 26 12 hfast

theorem zero_r26_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 13 := by decide +kernel
  exact zeroAtFast_sound 26 13 hfast

theorem zero_r26_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 14 := by decide +kernel
  exact zeroAtFast_sound 26 14 hfast

theorem zero_r26_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 15 := by decide +kernel
  exact zeroAtFast_sound 26 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
