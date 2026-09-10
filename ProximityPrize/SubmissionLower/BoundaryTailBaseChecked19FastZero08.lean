import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r19_part112 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 112 := by decide +kernel
  exact zeroAtFast_sound 19 112 hfast

theorem zero_r19_part113 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 113 := by decide +kernel
  exact zeroAtFast_sound 19 113 hfast

theorem zero_r19_part114 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 114 := by decide +kernel
  exact zeroAtFast_sound 19 114 hfast

theorem zero_r19_part115 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 115 := by decide +kernel
  exact zeroAtFast_sound 19 115 hfast

theorem zero_r19_part116 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 116 := by decide +kernel
  exact zeroAtFast_sound 19 116 hfast

theorem zero_r19_part117 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 117 := by decide +kernel
  exact zeroAtFast_sound 19 117 hfast

theorem zero_r19_part118 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 118 := by decide +kernel
  exact zeroAtFast_sound 19 118 hfast

theorem zero_r19_part119 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 119 := by decide +kernel
  exact zeroAtFast_sound 19 119 hfast

theorem zero_r19_part120 : ∀ i ∈ List.range 1, ZeroCheckAt 19 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 19 120 := by decide +kernel
  exact zeroAtFast_sound 19 120 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
