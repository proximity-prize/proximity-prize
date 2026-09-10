import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r17_part16 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 16 := by decide +kernel
  exact zeroAtFast_sound 17 16 hfast

theorem zero_r17_part17 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 17 := by decide +kernel
  exact zeroAtFast_sound 17 17 hfast

theorem zero_r17_part18 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 18 := by decide +kernel
  exact zeroAtFast_sound 17 18 hfast

theorem zero_r17_part19 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 19 := by decide +kernel
  exact zeroAtFast_sound 17 19 hfast

theorem zero_r17_part20 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 20 := by decide +kernel
  exact zeroAtFast_sound 17 20 hfast

theorem zero_r17_part21 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 21 := by decide +kernel
  exact zeroAtFast_sound 17 21 hfast

theorem zero_r17_part22 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 22 := by decide +kernel
  exact zeroAtFast_sound 17 22 hfast

theorem zero_r17_part23 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 23 := by decide +kernel
  exact zeroAtFast_sound 17 23 hfast

theorem zero_r17_part24 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 24 := by decide +kernel
  exact zeroAtFast_sound 17 24 hfast

theorem zero_r17_part25 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 25 := by decide +kernel
  exact zeroAtFast_sound 17 25 hfast

theorem zero_r17_part26 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 26 := by decide +kernel
  exact zeroAtFast_sound 17 26 hfast

theorem zero_r17_part27 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 27 := by decide +kernel
  exact zeroAtFast_sound 17 27 hfast

theorem zero_r17_part28 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 28 := by decide +kernel
  exact zeroAtFast_sound 17 28 hfast

theorem zero_r17_part29 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 29 := by decide +kernel
  exact zeroAtFast_sound 17 29 hfast

theorem zero_r17_part30 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 30 := by decide +kernel
  exact zeroAtFast_sound 17 30 hfast

theorem zero_r17_part31 : ∀ i ∈ List.range 1, ZeroCheckAt 17 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 17 31 := by decide +kernel
  exact zeroAtFast_sound 17 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
