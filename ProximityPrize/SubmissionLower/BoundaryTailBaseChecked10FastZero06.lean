import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r10_part80 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 80 := by decide +kernel
  exact zeroAtFast_sound 10 80 hfast

theorem zero_r10_part81 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 81 := by decide +kernel
  exact zeroAtFast_sound 10 81 hfast

theorem zero_r10_part82 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 82 := by decide +kernel
  exact zeroAtFast_sound 10 82 hfast

theorem zero_r10_part83 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 83 := by decide +kernel
  exact zeroAtFast_sound 10 83 hfast

theorem zero_r10_part84 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 84 := by decide +kernel
  exact zeroAtFast_sound 10 84 hfast

theorem zero_r10_part85 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 85 := by decide +kernel
  exact zeroAtFast_sound 10 85 hfast

theorem zero_r10_part86 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 86 := by decide +kernel
  exact zeroAtFast_sound 10 86 hfast

theorem zero_r10_part87 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 87 := by decide +kernel
  exact zeroAtFast_sound 10 87 hfast

theorem zero_r10_part88 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 88 := by decide +kernel
  exact zeroAtFast_sound 10 88 hfast

theorem zero_r10_part89 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 89 := by decide +kernel
  exact zeroAtFast_sound 10 89 hfast

theorem zero_r10_part90 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 90 := by decide +kernel
  exact zeroAtFast_sound 10 90 hfast

theorem zero_r10_part91 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 91 := by decide +kernel
  exact zeroAtFast_sound 10 91 hfast

theorem zero_r10_part92 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 92 := by decide +kernel
  exact zeroAtFast_sound 10 92 hfast

theorem zero_r10_part93 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 93 := by decide +kernel
  exact zeroAtFast_sound 10 93 hfast

theorem zero_r10_part94 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 94 := by decide +kernel
  exact zeroAtFast_sound 10 94 hfast

theorem zero_r10_part95 : ∀ i ∈ List.range 1, ZeroCheckAt 10 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 10 95 := by decide +kernel
  exact zeroAtFast_sound 10 95 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
