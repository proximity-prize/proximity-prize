import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r29_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 0 := by decide +kernel
  exact zeroAtFast_sound 29 0 hfast

theorem zero_r29_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 1 := by decide +kernel
  exact zeroAtFast_sound 29 1 hfast

theorem zero_r29_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 2 := by decide +kernel
  exact zeroAtFast_sound 29 2 hfast

theorem zero_r29_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 3 := by decide +kernel
  exact zeroAtFast_sound 29 3 hfast

theorem zero_r29_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 4 := by decide +kernel
  exact zeroAtFast_sound 29 4 hfast

theorem zero_r29_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 5 := by decide +kernel
  exact zeroAtFast_sound 29 5 hfast

theorem zero_r29_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 6 := by decide +kernel
  exact zeroAtFast_sound 29 6 hfast

theorem zero_r29_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 7 := by decide +kernel
  exact zeroAtFast_sound 29 7 hfast

theorem zero_r29_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 8 := by decide +kernel
  exact zeroAtFast_sound 29 8 hfast

theorem zero_r29_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 9 := by decide +kernel
  exact zeroAtFast_sound 29 9 hfast

theorem zero_r29_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 10 := by decide +kernel
  exact zeroAtFast_sound 29 10 hfast

theorem zero_r29_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 11 := by decide +kernel
  exact zeroAtFast_sound 29 11 hfast

theorem zero_r29_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 12 := by decide +kernel
  exact zeroAtFast_sound 29 12 hfast

theorem zero_r29_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 13 := by decide +kernel
  exact zeroAtFast_sound 29 13 hfast

theorem zero_r29_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 14 := by decide +kernel
  exact zeroAtFast_sound 29 14 hfast

theorem zero_r29_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 29 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 29 15 := by decide +kernel
  exact zeroAtFast_sound 29 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
