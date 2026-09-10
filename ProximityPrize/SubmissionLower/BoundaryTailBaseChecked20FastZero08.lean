import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r20_part112 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 112 := by decide +kernel
  exact zeroAtFast_sound 20 112 hfast

theorem zero_r20_part113 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 113 := by decide +kernel
  exact zeroAtFast_sound 20 113 hfast

theorem zero_r20_part114 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 114 := by decide +kernel
  exact zeroAtFast_sound 20 114 hfast

theorem zero_r20_part115 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 115 := by decide +kernel
  exact zeroAtFast_sound 20 115 hfast

theorem zero_r20_part116 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 116 := by decide +kernel
  exact zeroAtFast_sound 20 116 hfast

theorem zero_r20_part117 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 117 := by decide +kernel
  exact zeroAtFast_sound 20 117 hfast

theorem zero_r20_part118 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 118 := by decide +kernel
  exact zeroAtFast_sound 20 118 hfast

theorem zero_r20_part119 : ∀ i ∈ List.range 1, ZeroCheckAt 20 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 20 119 := by decide +kernel
  exact zeroAtFast_sound 20 119 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
