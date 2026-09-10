import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r8_part32 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (32+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 32 := by decide +kernel
  exact zeroAtFast_sound 8 32 hfast

theorem zero_r8_part33 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (33+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 33 := by decide +kernel
  exact zeroAtFast_sound 8 33 hfast

theorem zero_r8_part34 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (34+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 34 := by decide +kernel
  exact zeroAtFast_sound 8 34 hfast

theorem zero_r8_part35 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (35+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 35 := by decide +kernel
  exact zeroAtFast_sound 8 35 hfast

theorem zero_r8_part36 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (36+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 36 := by decide +kernel
  exact zeroAtFast_sound 8 36 hfast

theorem zero_r8_part37 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (37+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 37 := by decide +kernel
  exact zeroAtFast_sound 8 37 hfast

theorem zero_r8_part38 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (38+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 38 := by decide +kernel
  exact zeroAtFast_sound 8 38 hfast

theorem zero_r8_part39 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (39+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 39 := by decide +kernel
  exact zeroAtFast_sound 8 39 hfast

theorem zero_r8_part40 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (40+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 40 := by decide +kernel
  exact zeroAtFast_sound 8 40 hfast

theorem zero_r8_part41 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (41+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 41 := by decide +kernel
  exact zeroAtFast_sound 8 41 hfast

theorem zero_r8_part42 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (42+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 42 := by decide +kernel
  exact zeroAtFast_sound 8 42 hfast

theorem zero_r8_part43 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (43+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 43 := by decide +kernel
  exact zeroAtFast_sound 8 43 hfast

theorem zero_r8_part44 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (44+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 44 := by decide +kernel
  exact zeroAtFast_sound 8 44 hfast

theorem zero_r8_part45 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (45+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 45 := by decide +kernel
  exact zeroAtFast_sound 8 45 hfast

theorem zero_r8_part46 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (46+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 46 := by decide +kernel
  exact zeroAtFast_sound 8 46 hfast

theorem zero_r8_part47 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (47+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 47 := by decide +kernel
  exact zeroAtFast_sound 8 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
