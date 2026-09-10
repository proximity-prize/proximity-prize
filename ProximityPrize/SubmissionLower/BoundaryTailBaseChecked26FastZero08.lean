import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r26_part112 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 112 := by decide +kernel
  exact zeroAtFast_sound 26 112 hfast

theorem zero_r26_part113 : ∀ i ∈ List.range 1, ZeroCheckAt 26 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 26 113 := by decide +kernel
  exact zeroAtFast_sound 26 113 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
