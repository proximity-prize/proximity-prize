import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r22_part112 : ∀ i ∈ List.range 1, ZeroCheckAt 22 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 22 112 := by decide +kernel
  exact zeroAtFast_sound 22 112 hfast

theorem zero_r22_part113 : ∀ i ∈ List.range 1, ZeroCheckAt 22 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 22 113 := by decide +kernel
  exact zeroAtFast_sound 22 113 hfast

theorem zero_r22_part114 : ∀ i ∈ List.range 1, ZeroCheckAt 22 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 22 114 := by decide +kernel
  exact zeroAtFast_sound 22 114 hfast

theorem zero_r22_part115 : ∀ i ∈ List.range 1, ZeroCheckAt 22 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 22 115 := by decide +kernel
  exact zeroAtFast_sound 22 115 hfast

theorem zero_r22_part116 : ∀ i ∈ List.range 1, ZeroCheckAt 22 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 22 116 := by decide +kernel
  exact zeroAtFast_sound 22 116 hfast

theorem zero_r22_part117 : ∀ i ∈ List.range 1, ZeroCheckAt 22 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 22 117 := by decide +kernel
  exact zeroAtFast_sound 22 117 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
