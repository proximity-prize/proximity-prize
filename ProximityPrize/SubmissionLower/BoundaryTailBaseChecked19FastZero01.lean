import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r19_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 0 := by decide +kernel
  exact zeroAtFast_sound 19 0 hfast

theorem zero_r19_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 1 := by decide +kernel
  exact zeroAtFast_sound 19 1 hfast

theorem zero_r19_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 2 := by decide +kernel
  exact zeroAtFast_sound 19 2 hfast

theorem zero_r19_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 3 := by decide +kernel
  exact zeroAtFast_sound 19 3 hfast

theorem zero_r19_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 4 := by decide +kernel
  exact zeroAtFast_sound 19 4 hfast

theorem zero_r19_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 5 := by decide +kernel
  exact zeroAtFast_sound 19 5 hfast

theorem zero_r19_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 6 := by decide +kernel
  exact zeroAtFast_sound 19 6 hfast

theorem zero_r19_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 7 := by decide +kernel
  exact zeroAtFast_sound 19 7 hfast

theorem zero_r19_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 8 := by decide +kernel
  exact zeroAtFast_sound 19 8 hfast

theorem zero_r19_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 9 := by decide +kernel
  exact zeroAtFast_sound 19 9 hfast

theorem zero_r19_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 10 := by decide +kernel
  exact zeroAtFast_sound 19 10 hfast

theorem zero_r19_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 11 := by decide +kernel
  exact zeroAtFast_sound 19 11 hfast

theorem zero_r19_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 12 := by decide +kernel
  exact zeroAtFast_sound 19 12 hfast

theorem zero_r19_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 13 := by decide +kernel
  exact zeroAtFast_sound 19 13 hfast

theorem zero_r19_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 14 := by decide +kernel
  exact zeroAtFast_sound 19 14 hfast

theorem zero_r19_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 15 := by decide +kernel
  exact zeroAtFast_sound 19 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
