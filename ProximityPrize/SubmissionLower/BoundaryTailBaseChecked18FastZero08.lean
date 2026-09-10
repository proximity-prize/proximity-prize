import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r18_part112 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 112 := by decide +kernel
  exact zeroAtFast_sound 18 112 hfast

theorem zero_r18_part113 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 113 := by decide +kernel
  exact zeroAtFast_sound 18 113 hfast

theorem zero_r18_part114 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 114 := by decide +kernel
  exact zeroAtFast_sound 18 114 hfast

theorem zero_r18_part115 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 115 := by decide +kernel
  exact zeroAtFast_sound 18 115 hfast

theorem zero_r18_part116 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 116 := by decide +kernel
  exact zeroAtFast_sound 18 116 hfast

theorem zero_r18_part117 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 117 := by decide +kernel
  exact zeroAtFast_sound 18 117 hfast

theorem zero_r18_part118 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 118 := by decide +kernel
  exact zeroAtFast_sound 18 118 hfast

theorem zero_r18_part119 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 119 := by decide +kernel
  exact zeroAtFast_sound 18 119 hfast

theorem zero_r18_part120 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 120 := by decide +kernel
  exact zeroAtFast_sound 18 120 hfast

theorem zero_r18_part121 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 121 := by decide +kernel
  exact zeroAtFast_sound 18 121 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
