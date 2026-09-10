import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r9_part128 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (128+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 128 := by decide +kernel
  exact zeroAtFast_sound 9 128 hfast

theorem zero_r9_part129 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (129+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 129 := by decide +kernel
  exact zeroAtFast_sound 9 129 hfast

theorem zero_r9_part130 : ∀ i ∈ List.range 1, ZeroCheckAt 9 (130+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 9 130 := by decide +kernel
  exact zeroAtFast_sound 9 130 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
