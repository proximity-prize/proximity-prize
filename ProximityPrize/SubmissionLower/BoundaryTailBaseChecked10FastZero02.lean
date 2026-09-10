import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r10_part16 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 16 := by decide +kernel
  exact zeroAtFast_sound 10 16 hfast

theorem zero_r10_part17 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 17 := by decide +kernel
  exact zeroAtFast_sound 10 17 hfast

theorem zero_r10_part18 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 18 := by decide +kernel
  exact zeroAtFast_sound 10 18 hfast

theorem zero_r10_part19 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 19 := by decide +kernel
  exact zeroAtFast_sound 10 19 hfast

theorem zero_r10_part20 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 20 := by decide +kernel
  exact zeroAtFast_sound 10 20 hfast

theorem zero_r10_part21 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 21 := by decide +kernel
  exact zeroAtFast_sound 10 21 hfast

theorem zero_r10_part22 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 22 := by decide +kernel
  exact zeroAtFast_sound 10 22 hfast

theorem zero_r10_part23 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 23 := by decide +kernel
  exact zeroAtFast_sound 10 23 hfast

theorem zero_r10_part24 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 24 := by decide +kernel
  exact zeroAtFast_sound 10 24 hfast

theorem zero_r10_part25 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 25 := by decide +kernel
  exact zeroAtFast_sound 10 25 hfast

theorem zero_r10_part26 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 26 := by decide +kernel
  exact zeroAtFast_sound 10 26 hfast

theorem zero_r10_part27 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 27 := by decide +kernel
  exact zeroAtFast_sound 10 27 hfast

theorem zero_r10_part28 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 28 := by decide +kernel
  exact zeroAtFast_sound 10 28 hfast

theorem zero_r10_part29 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 29 := by decide +kernel
  exact zeroAtFast_sound 10 29 hfast

theorem zero_r10_part30 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 30 := by decide +kernel
  exact zeroAtFast_sound 10 30 hfast

theorem zero_r10_part31 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 31 := by decide +kernel
  exact zeroAtFast_sound 10 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
