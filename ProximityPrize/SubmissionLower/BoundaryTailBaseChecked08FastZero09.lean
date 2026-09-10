import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r8_part128 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (128+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 128 := by decide +kernel
  exact zeroAtFast_sound 8 128 hfast

theorem zero_r8_part129 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (129+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 129 := by decide +kernel
  exact zeroAtFast_sound 8 129 hfast

theorem zero_r8_part130 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (130+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 130 := by decide +kernel
  exact zeroAtFast_sound 8 130 hfast

theorem zero_r8_part131 : ∀ i ∈ List.range 1, ZeroCheckAt 8 (131+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 8 131 := by decide +kernel
  exact zeroAtFast_sound 8 131 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
