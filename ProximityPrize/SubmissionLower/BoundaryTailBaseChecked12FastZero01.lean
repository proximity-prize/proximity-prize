import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r12_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 0 := by decide +kernel
  exact zeroAtFast_sound 12 0 hfast

theorem zero_r12_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 1 := by decide +kernel
  exact zeroAtFast_sound 12 1 hfast

theorem zero_r12_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 2 := by decide +kernel
  exact zeroAtFast_sound 12 2 hfast

theorem zero_r12_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 3 := by decide +kernel
  exact zeroAtFast_sound 12 3 hfast

theorem zero_r12_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 4 := by decide +kernel
  exact zeroAtFast_sound 12 4 hfast

theorem zero_r12_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 5 := by decide +kernel
  exact zeroAtFast_sound 12 5 hfast

theorem zero_r12_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 6 := by decide +kernel
  exact zeroAtFast_sound 12 6 hfast

theorem zero_r12_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 7 := by decide +kernel
  exact zeroAtFast_sound 12 7 hfast

theorem zero_r12_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 8 := by decide +kernel
  exact zeroAtFast_sound 12 8 hfast

theorem zero_r12_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 9 := by decide +kernel
  exact zeroAtFast_sound 12 9 hfast

theorem zero_r12_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 10 := by decide +kernel
  exact zeroAtFast_sound 12 10 hfast

theorem zero_r12_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 11 := by decide +kernel
  exact zeroAtFast_sound 12 11 hfast

theorem zero_r12_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 12 := by decide +kernel
  exact zeroAtFast_sound 12 12 hfast

theorem zero_r12_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 13 := by decide +kernel
  exact zeroAtFast_sound 12 13 hfast

theorem zero_r12_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 14 := by decide +kernel
  exact zeroAtFast_sound 12 14 hfast

theorem zero_r12_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 12 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 12 15 := by decide +kernel
  exact zeroAtFast_sound 12 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
