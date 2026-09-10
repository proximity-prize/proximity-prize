import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r16_part64 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 64 := by decide +kernel
  exact zeroAtFast_sound 16 64 hfast

theorem zero_r16_part65 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 65 := by decide +kernel
  exact zeroAtFast_sound 16 65 hfast

theorem zero_r16_part66 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 66 := by decide +kernel
  exact zeroAtFast_sound 16 66 hfast

theorem zero_r16_part67 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 67 := by decide +kernel
  exact zeroAtFast_sound 16 67 hfast

theorem zero_r16_part68 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 68 := by decide +kernel
  exact zeroAtFast_sound 16 68 hfast

theorem zero_r16_part69 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 69 := by decide +kernel
  exact zeroAtFast_sound 16 69 hfast

theorem zero_r16_part70 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 70 := by decide +kernel
  exact zeroAtFast_sound 16 70 hfast

theorem zero_r16_part71 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 71 := by decide +kernel
  exact zeroAtFast_sound 16 71 hfast

theorem zero_r16_part72 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 72 := by decide +kernel
  exact zeroAtFast_sound 16 72 hfast

theorem zero_r16_part73 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 73 := by decide +kernel
  exact zeroAtFast_sound 16 73 hfast

theorem zero_r16_part74 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 74 := by decide +kernel
  exact zeroAtFast_sound 16 74 hfast

theorem zero_r16_part75 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 75 := by decide +kernel
  exact zeroAtFast_sound 16 75 hfast

theorem zero_r16_part76 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 76 := by decide +kernel
  exact zeroAtFast_sound 16 76 hfast

theorem zero_r16_part77 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 77 := by decide +kernel
  exact zeroAtFast_sound 16 77 hfast

theorem zero_r16_part78 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 78 := by decide +kernel
  exact zeroAtFast_sound 16 78 hfast

theorem zero_r16_part79 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 79 := by decide +kernel
  exact zeroAtFast_sound 16 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
