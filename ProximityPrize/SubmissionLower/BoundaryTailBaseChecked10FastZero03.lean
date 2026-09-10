import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r10_part32 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (32+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 32 := by decide +kernel
  exact zeroAtFast_sound 10 32 hfast

theorem zero_r10_part33 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (33+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 33 := by decide +kernel
  exact zeroAtFast_sound 10 33 hfast

theorem zero_r10_part34 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (34+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 34 := by decide +kernel
  exact zeroAtFast_sound 10 34 hfast

theorem zero_r10_part35 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (35+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 35 := by decide +kernel
  exact zeroAtFast_sound 10 35 hfast

theorem zero_r10_part36 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (36+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 36 := by decide +kernel
  exact zeroAtFast_sound 10 36 hfast

theorem zero_r10_part37 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (37+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 37 := by decide +kernel
  exact zeroAtFast_sound 10 37 hfast

theorem zero_r10_part38 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (38+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 38 := by decide +kernel
  exact zeroAtFast_sound 10 38 hfast

theorem zero_r10_part39 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (39+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 39 := by decide +kernel
  exact zeroAtFast_sound 10 39 hfast

theorem zero_r10_part40 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (40+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 40 := by decide +kernel
  exact zeroAtFast_sound 10 40 hfast

theorem zero_r10_part41 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (41+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 41 := by decide +kernel
  exact zeroAtFast_sound 10 41 hfast

theorem zero_r10_part42 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (42+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 42 := by decide +kernel
  exact zeroAtFast_sound 10 42 hfast

theorem zero_r10_part43 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (43+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 43 := by decide +kernel
  exact zeroAtFast_sound 10 43 hfast

theorem zero_r10_part44 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (44+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 44 := by decide +kernel
  exact zeroAtFast_sound 10 44 hfast

theorem zero_r10_part45 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (45+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 45 := by decide +kernel
  exact zeroAtFast_sound 10 45 hfast

theorem zero_r10_part46 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (46+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 46 := by decide +kernel
  exact zeroAtFast_sound 10 46 hfast

theorem zero_r10_part47 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (47+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 47 := by decide +kernel
  exact zeroAtFast_sound 10 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
