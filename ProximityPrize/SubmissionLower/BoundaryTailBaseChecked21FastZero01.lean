import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r21_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 0 := by decide +kernel
  exact zeroAtFast_sound 21 0 hfast

theorem zero_r21_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 1 := by decide +kernel
  exact zeroAtFast_sound 21 1 hfast

theorem zero_r21_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 2 := by decide +kernel
  exact zeroAtFast_sound 21 2 hfast

theorem zero_r21_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 3 := by decide +kernel
  exact zeroAtFast_sound 21 3 hfast

theorem zero_r21_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 4 := by decide +kernel
  exact zeroAtFast_sound 21 4 hfast

theorem zero_r21_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 5 := by decide +kernel
  exact zeroAtFast_sound 21 5 hfast

theorem zero_r21_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 6 := by decide +kernel
  exact zeroAtFast_sound 21 6 hfast

theorem zero_r21_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 7 := by decide +kernel
  exact zeroAtFast_sound 21 7 hfast

theorem zero_r21_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 8 := by decide +kernel
  exact zeroAtFast_sound 21 8 hfast

theorem zero_r21_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 9 := by decide +kernel
  exact zeroAtFast_sound 21 9 hfast

theorem zero_r21_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 10 := by decide +kernel
  exact zeroAtFast_sound 21 10 hfast

theorem zero_r21_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 11 := by decide +kernel
  exact zeroAtFast_sound 21 11 hfast

theorem zero_r21_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 12 := by decide +kernel
  exact zeroAtFast_sound 21 12 hfast

theorem zero_r21_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 13 := by decide +kernel
  exact zeroAtFast_sound 21 13 hfast

theorem zero_r21_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 14 := by decide +kernel
  exact zeroAtFast_sound 21 14 hfast

theorem zero_r21_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 21 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 21 15 := by decide +kernel
  exact zeroAtFast_sound 21 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
