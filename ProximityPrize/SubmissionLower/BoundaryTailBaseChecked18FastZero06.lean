import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r18_part80 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 80 := by decide +kernel
  exact zeroAtFast_sound 18 80 hfast

theorem zero_r18_part81 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 81 := by decide +kernel
  exact zeroAtFast_sound 18 81 hfast

theorem zero_r18_part82 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 82 := by decide +kernel
  exact zeroAtFast_sound 18 82 hfast

theorem zero_r18_part83 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 83 := by decide +kernel
  exact zeroAtFast_sound 18 83 hfast

theorem zero_r18_part84 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 84 := by decide +kernel
  exact zeroAtFast_sound 18 84 hfast

theorem zero_r18_part85 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 85 := by decide +kernel
  exact zeroAtFast_sound 18 85 hfast

theorem zero_r18_part86 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 86 := by decide +kernel
  exact zeroAtFast_sound 18 86 hfast

theorem zero_r18_part87 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 87 := by decide +kernel
  exact zeroAtFast_sound 18 87 hfast

theorem zero_r18_part88 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 88 := by decide +kernel
  exact zeroAtFast_sound 18 88 hfast

theorem zero_r18_part89 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 89 := by decide +kernel
  exact zeroAtFast_sound 18 89 hfast

theorem zero_r18_part90 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 90 := by decide +kernel
  exact zeroAtFast_sound 18 90 hfast

theorem zero_r18_part91 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 91 := by decide +kernel
  exact zeroAtFast_sound 18 91 hfast

theorem zero_r18_part92 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 92 := by decide +kernel
  exact zeroAtFast_sound 18 92 hfast

theorem zero_r18_part93 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 93 := by decide +kernel
  exact zeroAtFast_sound 18 93 hfast

theorem zero_r18_part94 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 94 := by decide +kernel
  exact zeroAtFast_sound 18 94 hfast

theorem zero_r18_part95 : ∀ i ∈ List.range 1, ZeroCheckAt 18 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 18 95 := by decide +kernel
  exact zeroAtFast_sound 18 95 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
