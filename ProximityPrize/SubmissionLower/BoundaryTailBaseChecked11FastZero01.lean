import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r11_part0 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 0 := by decide +kernel
  exact zeroAtFast_sound 11 0 hfast

theorem zero_r11_part1 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 1 := by decide +kernel
  exact zeroAtFast_sound 11 1 hfast

theorem zero_r11_part2 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 2 := by decide +kernel
  exact zeroAtFast_sound 11 2 hfast

theorem zero_r11_part3 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 3 := by decide +kernel
  exact zeroAtFast_sound 11 3 hfast

theorem zero_r11_part4 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 4 := by decide +kernel
  exact zeroAtFast_sound 11 4 hfast

theorem zero_r11_part5 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 5 := by decide +kernel
  exact zeroAtFast_sound 11 5 hfast

theorem zero_r11_part6 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 6 := by decide +kernel
  exact zeroAtFast_sound 11 6 hfast

theorem zero_r11_part7 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 7 := by decide +kernel
  exact zeroAtFast_sound 11 7 hfast

theorem zero_r11_part8 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 8 := by decide +kernel
  exact zeroAtFast_sound 11 8 hfast

theorem zero_r11_part9 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 9 := by decide +kernel
  exact zeroAtFast_sound 11 9 hfast

theorem zero_r11_part10 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 10 := by decide +kernel
  exact zeroAtFast_sound 11 10 hfast

theorem zero_r11_part11 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 11 := by decide +kernel
  exact zeroAtFast_sound 11 11 hfast

theorem zero_r11_part12 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 12 := by decide +kernel
  exact zeroAtFast_sound 11 12 hfast

theorem zero_r11_part13 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 13 := by decide +kernel
  exact zeroAtFast_sound 11 13 hfast

theorem zero_r11_part14 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 14 := by decide +kernel
  exact zeroAtFast_sound 11 14 hfast

theorem zero_r11_part15 : ∀ i ∈ List.range 1, ZeroCheckAt 11 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 11 15 := by decide +kernel
  exact zeroAtFast_sound 11 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
