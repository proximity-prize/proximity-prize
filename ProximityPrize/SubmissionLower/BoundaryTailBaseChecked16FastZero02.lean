import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r16_part16 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 16 := by decide +kernel
  exact zeroAtFast_sound 16 16 hfast

theorem zero_r16_part17 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 17 := by decide +kernel
  exact zeroAtFast_sound 16 17 hfast

theorem zero_r16_part18 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 18 := by decide +kernel
  exact zeroAtFast_sound 16 18 hfast

theorem zero_r16_part19 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 19 := by decide +kernel
  exact zeroAtFast_sound 16 19 hfast

theorem zero_r16_part20 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 20 := by decide +kernel
  exact zeroAtFast_sound 16 20 hfast

theorem zero_r16_part21 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 21 := by decide +kernel
  exact zeroAtFast_sound 16 21 hfast

theorem zero_r16_part22 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 22 := by decide +kernel
  exact zeroAtFast_sound 16 22 hfast

theorem zero_r16_part23 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 23 := by decide +kernel
  exact zeroAtFast_sound 16 23 hfast

theorem zero_r16_part24 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 24 := by decide +kernel
  exact zeroAtFast_sound 16 24 hfast

theorem zero_r16_part25 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 25 := by decide +kernel
  exact zeroAtFast_sound 16 25 hfast

theorem zero_r16_part26 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 26 := by decide +kernel
  exact zeroAtFast_sound 16 26 hfast

theorem zero_r16_part27 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 27 := by decide +kernel
  exact zeroAtFast_sound 16 27 hfast

theorem zero_r16_part28 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 28 := by decide +kernel
  exact zeroAtFast_sound 16 28 hfast

theorem zero_r16_part29 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 29 := by decide +kernel
  exact zeroAtFast_sound 16 29 hfast

theorem zero_r16_part30 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 30 := by decide +kernel
  exact zeroAtFast_sound 16 30 hfast

theorem zero_r16_part31 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 31 := by decide +kernel
  exact zeroAtFast_sound 16 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
