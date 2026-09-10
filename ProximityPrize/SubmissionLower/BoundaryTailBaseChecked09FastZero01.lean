import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r9_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 0 := by decide +kernel
  exact zeroAtFast_sound 9 0 hfast

theorem zero_r9_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 1 := by decide +kernel
  exact zeroAtFast_sound 9 1 hfast

theorem zero_r9_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 2 := by decide +kernel
  exact zeroAtFast_sound 9 2 hfast

theorem zero_r9_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 3 := by decide +kernel
  exact zeroAtFast_sound 9 3 hfast

theorem zero_r9_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 4 := by decide +kernel
  exact zeroAtFast_sound 9 4 hfast

theorem zero_r9_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 5 := by decide +kernel
  exact zeroAtFast_sound 9 5 hfast

theorem zero_r9_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 6 := by decide +kernel
  exact zeroAtFast_sound 9 6 hfast

theorem zero_r9_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 7 := by decide +kernel
  exact zeroAtFast_sound 9 7 hfast

theorem zero_r9_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 8 := by decide +kernel
  exact zeroAtFast_sound 9 8 hfast

theorem zero_r9_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 9 := by decide +kernel
  exact zeroAtFast_sound 9 9 hfast

theorem zero_r9_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 10 := by decide +kernel
  exact zeroAtFast_sound 9 10 hfast

theorem zero_r9_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 11 := by decide +kernel
  exact zeroAtFast_sound 9 11 hfast

theorem zero_r9_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 12 := by decide +kernel
  exact zeroAtFast_sound 9 12 hfast

theorem zero_r9_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 13 := by decide +kernel
  exact zeroAtFast_sound 9 13 hfast

theorem zero_r9_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 14 := by decide +kernel
  exact zeroAtFast_sound 9 14 hfast

theorem zero_r9_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 15 := by decide +kernel
  exact zeroAtFast_sound 9 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
