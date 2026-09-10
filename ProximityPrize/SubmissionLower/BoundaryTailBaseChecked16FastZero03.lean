import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r16_part32 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (32+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 32 := by decide +kernel
  exact zeroAtFast_sound 16 32 hfast

theorem zero_r16_part33 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (33+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 33 := by decide +kernel
  exact zeroAtFast_sound 16 33 hfast

theorem zero_r16_part34 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (34+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 34 := by decide +kernel
  exact zeroAtFast_sound 16 34 hfast

theorem zero_r16_part35 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (35+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 35 := by decide +kernel
  exact zeroAtFast_sound 16 35 hfast

theorem zero_r16_part36 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (36+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 36 := by decide +kernel
  exact zeroAtFast_sound 16 36 hfast

theorem zero_r16_part37 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (37+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 37 := by decide +kernel
  exact zeroAtFast_sound 16 37 hfast

theorem zero_r16_part38 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (38+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 38 := by decide +kernel
  exact zeroAtFast_sound 16 38 hfast

theorem zero_r16_part39 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (39+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 39 := by decide +kernel
  exact zeroAtFast_sound 16 39 hfast

theorem zero_r16_part40 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (40+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 40 := by decide +kernel
  exact zeroAtFast_sound 16 40 hfast

theorem zero_r16_part41 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (41+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 41 := by decide +kernel
  exact zeroAtFast_sound 16 41 hfast

theorem zero_r16_part42 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (42+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 42 := by decide +kernel
  exact zeroAtFast_sound 16 42 hfast

theorem zero_r16_part43 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (43+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 43 := by decide +kernel
  exact zeroAtFast_sound 16 43 hfast

theorem zero_r16_part44 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (44+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 44 := by decide +kernel
  exact zeroAtFast_sound 16 44 hfast

theorem zero_r16_part45 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (45+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 45 := by decide +kernel
  exact zeroAtFast_sound 16 45 hfast

theorem zero_r16_part46 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (46+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 46 := by decide +kernel
  exact zeroAtFast_sound 16 46 hfast

theorem zero_r16_part47 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (47+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 47 := by decide +kernel
  exact zeroAtFast_sound 16 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
