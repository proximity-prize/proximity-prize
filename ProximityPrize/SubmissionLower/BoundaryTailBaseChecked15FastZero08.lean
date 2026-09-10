import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r15_part112 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 112 := by decide +kernel
  exact zeroAtFast_sound 15 112 hfast

theorem zero_r15_part113 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 113 := by decide +kernel
  exact zeroAtFast_sound 15 113 hfast

theorem zero_r15_part114 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 114 := by decide +kernel
  exact zeroAtFast_sound 15 114 hfast

theorem zero_r15_part115 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 115 := by decide +kernel
  exact zeroAtFast_sound 15 115 hfast

theorem zero_r15_part116 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 116 := by decide +kernel
  exact zeroAtFast_sound 15 116 hfast

theorem zero_r15_part117 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 117 := by decide +kernel
  exact zeroAtFast_sound 15 117 hfast

theorem zero_r15_part118 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 118 := by decide +kernel
  exact zeroAtFast_sound 15 118 hfast

theorem zero_r15_part119 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 119 := by decide +kernel
  exact zeroAtFast_sound 15 119 hfast

theorem zero_r15_part120 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 120 := by decide +kernel
  exact zeroAtFast_sound 15 120 hfast

theorem zero_r15_part121 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 121 := by decide +kernel
  exact zeroAtFast_sound 15 121 hfast

theorem zero_r15_part122 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (122+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 122 := by decide +kernel
  exact zeroAtFast_sound 15 122 hfast

theorem zero_r15_part123 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (123+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 123 := by decide +kernel
  exact zeroAtFast_sound 15 123 hfast

theorem zero_r15_part124 : ∀ i ∈ List.range 1, ZeroCheckAt 15 (124+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 15 124 := by decide +kernel
  exact zeroAtFast_sound 15 124 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
