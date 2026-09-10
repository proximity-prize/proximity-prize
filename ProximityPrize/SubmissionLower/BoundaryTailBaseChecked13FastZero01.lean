import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r13_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 0 := by decide +kernel
  exact zeroAtFast_sound 13 0 hfast

theorem zero_r13_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 1 := by decide +kernel
  exact zeroAtFast_sound 13 1 hfast

theorem zero_r13_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 2 := by decide +kernel
  exact zeroAtFast_sound 13 2 hfast

theorem zero_r13_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 3 := by decide +kernel
  exact zeroAtFast_sound 13 3 hfast

theorem zero_r13_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 4 := by decide +kernel
  exact zeroAtFast_sound 13 4 hfast

theorem zero_r13_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 5 := by decide +kernel
  exact zeroAtFast_sound 13 5 hfast

theorem zero_r13_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 6 := by decide +kernel
  exact zeroAtFast_sound 13 6 hfast

theorem zero_r13_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 7 := by decide +kernel
  exact zeroAtFast_sound 13 7 hfast

theorem zero_r13_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 8 := by decide +kernel
  exact zeroAtFast_sound 13 8 hfast

theorem zero_r13_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 9 := by decide +kernel
  exact zeroAtFast_sound 13 9 hfast

theorem zero_r13_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 10 := by decide +kernel
  exact zeroAtFast_sound 13 10 hfast

theorem zero_r13_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 11 := by decide +kernel
  exact zeroAtFast_sound 13 11 hfast

theorem zero_r13_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 12 := by decide +kernel
  exact zeroAtFast_sound 13 12 hfast

theorem zero_r13_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 13 := by decide +kernel
  exact zeroAtFast_sound 13 13 hfast

theorem zero_r13_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 14 := by decide +kernel
  exact zeroAtFast_sound 13 14 hfast

theorem zero_r13_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 13 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 13 15 := by decide +kernel
  exact zeroAtFast_sound 13 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
