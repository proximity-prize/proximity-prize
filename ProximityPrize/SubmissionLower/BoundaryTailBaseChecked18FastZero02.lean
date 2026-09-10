import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r18_part16 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 16 := by decide +kernel
  exact zeroAtFast_sound 18 16 hfast

theorem zero_r18_part17 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 17 := by decide +kernel
  exact zeroAtFast_sound 18 17 hfast

theorem zero_r18_part18 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 18 := by decide +kernel
  exact zeroAtFast_sound 18 18 hfast

theorem zero_r18_part19 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 19 := by decide +kernel
  exact zeroAtFast_sound 18 19 hfast

theorem zero_r18_part20 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 20 := by decide +kernel
  exact zeroAtFast_sound 18 20 hfast

theorem zero_r18_part21 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 21 := by decide +kernel
  exact zeroAtFast_sound 18 21 hfast

theorem zero_r18_part22 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 22 := by decide +kernel
  exact zeroAtFast_sound 18 22 hfast

theorem zero_r18_part23 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 23 := by decide +kernel
  exact zeroAtFast_sound 18 23 hfast

theorem zero_r18_part24 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 24 := by decide +kernel
  exact zeroAtFast_sound 18 24 hfast

theorem zero_r18_part25 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 25 := by decide +kernel
  exact zeroAtFast_sound 18 25 hfast

theorem zero_r18_part26 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 26 := by decide +kernel
  exact zeroAtFast_sound 18 26 hfast

theorem zero_r18_part27 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 27 := by decide +kernel
  exact zeroAtFast_sound 18 27 hfast

theorem zero_r18_part28 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 28 := by decide +kernel
  exact zeroAtFast_sound 18 28 hfast

theorem zero_r18_part29 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 29 := by decide +kernel
  exact zeroAtFast_sound 18 29 hfast

theorem zero_r18_part30 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 30 := by decide +kernel
  exact zeroAtFast_sound 18 30 hfast

theorem zero_r18_part31 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 31 := by decide +kernel
  exact zeroAtFast_sound 18 31 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
