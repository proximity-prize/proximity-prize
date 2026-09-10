import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r18_part64 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 64 := by decide +kernel
  exact zeroAtFast_sound 18 64 hfast

theorem zero_r18_part65 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 65 := by decide +kernel
  exact zeroAtFast_sound 18 65 hfast

theorem zero_r18_part66 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 66 := by decide +kernel
  exact zeroAtFast_sound 18 66 hfast

theorem zero_r18_part67 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 67 := by decide +kernel
  exact zeroAtFast_sound 18 67 hfast

theorem zero_r18_part68 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 68 := by decide +kernel
  exact zeroAtFast_sound 18 68 hfast

theorem zero_r18_part69 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 69 := by decide +kernel
  exact zeroAtFast_sound 18 69 hfast

theorem zero_r18_part70 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 70 := by decide +kernel
  exact zeroAtFast_sound 18 70 hfast

theorem zero_r18_part71 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 71 := by decide +kernel
  exact zeroAtFast_sound 18 71 hfast

theorem zero_r18_part72 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 72 := by decide +kernel
  exact zeroAtFast_sound 18 72 hfast

theorem zero_r18_part73 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 73 := by decide +kernel
  exact zeroAtFast_sound 18 73 hfast

theorem zero_r18_part74 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 74 := by decide +kernel
  exact zeroAtFast_sound 18 74 hfast

theorem zero_r18_part75 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 75 := by decide +kernel
  exact zeroAtFast_sound 18 75 hfast

theorem zero_r18_part76 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 76 := by decide +kernel
  exact zeroAtFast_sound 18 76 hfast

theorem zero_r18_part77 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 77 := by decide +kernel
  exact zeroAtFast_sound 18 77 hfast

theorem zero_r18_part78 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 78 := by decide +kernel
  exact zeroAtFast_sound 18 78 hfast

theorem zero_r18_part79 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 79 := by decide +kernel
  exact zeroAtFast_sound 18 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
