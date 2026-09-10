import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r8_part16 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 16 := by decide +kernel
  exact zeroAtFast_sound 8 16 hfast

theorem zero_r8_part17 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 17 := by decide +kernel
  exact zeroAtFast_sound 8 17 hfast

theorem zero_r8_part18 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 18 := by decide +kernel
  exact zeroAtFast_sound 8 18 hfast

theorem zero_r8_part19 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 19 := by decide +kernel
  exact zeroAtFast_sound 8 19 hfast

theorem zero_r8_part20 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 20 := by decide +kernel
  exact zeroAtFast_sound 8 20 hfast

theorem zero_r8_part21 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 21 := by decide +kernel
  exact zeroAtFast_sound 8 21 hfast

theorem zero_r8_part22 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 22 := by decide +kernel
  exact zeroAtFast_sound 8 22 hfast

theorem zero_r8_part23 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 23 := by decide +kernel
  exact zeroAtFast_sound 8 23 hfast

theorem zero_r8_part24 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 24 := by decide +kernel
  exact zeroAtFast_sound 8 24 hfast

theorem zero_r8_part25 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 25 := by decide +kernel
  exact zeroAtFast_sound 8 25 hfast

theorem zero_r8_part26 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 26 := by decide +kernel
  exact zeroAtFast_sound 8 26 hfast

theorem zero_r8_part27 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 27 := by decide +kernel
  exact zeroAtFast_sound 8 27 hfast

theorem zero_r8_part28 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 28 := by decide +kernel
  exact zeroAtFast_sound 8 28 hfast

theorem zero_r8_part29 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 29 := by decide +kernel
  exact zeroAtFast_sound 8 29 hfast

theorem zero_r8_part30 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 30 := by decide +kernel
  exact zeroAtFast_sound 8 30 hfast

theorem zero_r8_part31 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 31 := by decide +kernel
  exact zeroAtFast_sound 8 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
