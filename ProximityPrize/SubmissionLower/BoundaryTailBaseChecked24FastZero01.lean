import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r24_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 0 := by decide +kernel
  exact zeroAtFast_sound 24 0 hfast

theorem zero_r24_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 1 := by decide +kernel
  exact zeroAtFast_sound 24 1 hfast

theorem zero_r24_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 2 := by decide +kernel
  exact zeroAtFast_sound 24 2 hfast

theorem zero_r24_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 3 := by decide +kernel
  exact zeroAtFast_sound 24 3 hfast

theorem zero_r24_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 4 := by decide +kernel
  exact zeroAtFast_sound 24 4 hfast

theorem zero_r24_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 5 := by decide +kernel
  exact zeroAtFast_sound 24 5 hfast

theorem zero_r24_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 6 := by decide +kernel
  exact zeroAtFast_sound 24 6 hfast

theorem zero_r24_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 7 := by decide +kernel
  exact zeroAtFast_sound 24 7 hfast

theorem zero_r24_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 8 := by decide +kernel
  exact zeroAtFast_sound 24 8 hfast

theorem zero_r24_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 9 := by decide +kernel
  exact zeroAtFast_sound 24 9 hfast

theorem zero_r24_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 10 := by decide +kernel
  exact zeroAtFast_sound 24 10 hfast

theorem zero_r24_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 11 := by decide +kernel
  exact zeroAtFast_sound 24 11 hfast

theorem zero_r24_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 12 := by decide +kernel
  exact zeroAtFast_sound 24 12 hfast

theorem zero_r24_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 13 := by decide +kernel
  exact zeroAtFast_sound 24 13 hfast

theorem zero_r24_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 14 := by decide +kernel
  exact zeroAtFast_sound 24 14 hfast

theorem zero_r24_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 24 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 24 15 := by decide +kernel
  exact zeroAtFast_sound 24 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
