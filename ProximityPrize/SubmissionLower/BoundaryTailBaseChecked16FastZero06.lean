import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r16_part80 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 80 := by decide +kernel
  exact zeroAtFast_sound 16 80 hfast

theorem zero_r16_part81 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 81 := by decide +kernel
  exact zeroAtFast_sound 16 81 hfast

theorem zero_r16_part82 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 82 := by decide +kernel
  exact zeroAtFast_sound 16 82 hfast

theorem zero_r16_part83 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 83 := by decide +kernel
  exact zeroAtFast_sound 16 83 hfast

theorem zero_r16_part84 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 84 := by decide +kernel
  exact zeroAtFast_sound 16 84 hfast

theorem zero_r16_part85 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 85 := by decide +kernel
  exact zeroAtFast_sound 16 85 hfast

theorem zero_r16_part86 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 86 := by decide +kernel
  exact zeroAtFast_sound 16 86 hfast

theorem zero_r16_part87 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 87 := by decide +kernel
  exact zeroAtFast_sound 16 87 hfast

theorem zero_r16_part88 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 88 := by decide +kernel
  exact zeroAtFast_sound 16 88 hfast

theorem zero_r16_part89 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 89 := by decide +kernel
  exact zeroAtFast_sound 16 89 hfast

theorem zero_r16_part90 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 90 := by decide +kernel
  exact zeroAtFast_sound 16 90 hfast

theorem zero_r16_part91 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 91 := by decide +kernel
  exact zeroAtFast_sound 16 91 hfast

theorem zero_r16_part92 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 92 := by decide +kernel
  exact zeroAtFast_sound 16 92 hfast

theorem zero_r16_part93 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 93 := by decide +kernel
  exact zeroAtFast_sound 16 93 hfast

theorem zero_r16_part94 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 94 := by decide +kernel
  exact zeroAtFast_sound 16 94 hfast

theorem zero_r16_part95 : ∀ i ∈ List.range 1, ZeroCheckAt 16 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 16 95 := by decide +kernel
  exact zeroAtFast_sound 16 95 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
