import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r18_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 0 := by decide +kernel
  exact zeroAtFast_sound 18 0 hfast

theorem zero_r18_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 1 := by decide +kernel
  exact zeroAtFast_sound 18 1 hfast

theorem zero_r18_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 2 := by decide +kernel
  exact zeroAtFast_sound 18 2 hfast

theorem zero_r18_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 3 := by decide +kernel
  exact zeroAtFast_sound 18 3 hfast

theorem zero_r18_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 4 := by decide +kernel
  exact zeroAtFast_sound 18 4 hfast

theorem zero_r18_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 5 := by decide +kernel
  exact zeroAtFast_sound 18 5 hfast

theorem zero_r18_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 6 := by decide +kernel
  exact zeroAtFast_sound 18 6 hfast

theorem zero_r18_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 7 := by decide +kernel
  exact zeroAtFast_sound 18 7 hfast

theorem zero_r18_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 8 := by decide +kernel
  exact zeroAtFast_sound 18 8 hfast

theorem zero_r18_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 9 := by decide +kernel
  exact zeroAtFast_sound 18 9 hfast

theorem zero_r18_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 10 := by decide +kernel
  exact zeroAtFast_sound 18 10 hfast

theorem zero_r18_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 11 := by decide +kernel
  exact zeroAtFast_sound 18 11 hfast

theorem zero_r18_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 12 := by decide +kernel
  exact zeroAtFast_sound 18 12 hfast

theorem zero_r18_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 13 := by decide +kernel
  exact zeroAtFast_sound 18 13 hfast

theorem zero_r18_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 14 := by decide +kernel
  exact zeroAtFast_sound 18 14 hfast

theorem zero_r18_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 15 := by decide +kernel
  exact zeroAtFast_sound 18 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
