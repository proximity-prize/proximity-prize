import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r10_part64 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 64 := by decide +kernel
  exact zeroAtFast_sound 10 64 hfast

theorem zero_r10_part65 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 65 := by decide +kernel
  exact zeroAtFast_sound 10 65 hfast

theorem zero_r10_part66 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 66 := by decide +kernel
  exact zeroAtFast_sound 10 66 hfast

theorem zero_r10_part67 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 67 := by decide +kernel
  exact zeroAtFast_sound 10 67 hfast

theorem zero_r10_part68 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 68 := by decide +kernel
  exact zeroAtFast_sound 10 68 hfast

theorem zero_r10_part69 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 69 := by decide +kernel
  exact zeroAtFast_sound 10 69 hfast

theorem zero_r10_part70 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 70 := by decide +kernel
  exact zeroAtFast_sound 10 70 hfast

theorem zero_r10_part71 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 71 := by decide +kernel
  exact zeroAtFast_sound 10 71 hfast

theorem zero_r10_part72 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 72 := by decide +kernel
  exact zeroAtFast_sound 10 72 hfast

theorem zero_r10_part73 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 73 := by decide +kernel
  exact zeroAtFast_sound 10 73 hfast

theorem zero_r10_part74 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 74 := by decide +kernel
  exact zeroAtFast_sound 10 74 hfast

theorem zero_r10_part75 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 75 := by decide +kernel
  exact zeroAtFast_sound 10 75 hfast

theorem zero_r10_part76 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 76 := by decide +kernel
  exact zeroAtFast_sound 10 76 hfast

theorem zero_r10_part77 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 77 := by decide +kernel
  exact zeroAtFast_sound 10 77 hfast

theorem zero_r10_part78 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 78 := by decide +kernel
  exact zeroAtFast_sound 10 78 hfast

theorem zero_r10_part79 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 79 := by decide +kernel
  exact zeroAtFast_sound 10 79 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
