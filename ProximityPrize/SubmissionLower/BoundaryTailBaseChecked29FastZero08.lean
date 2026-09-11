import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr29p112:∀ i ∈ List.range 1,ZeroCheckAt 29 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 29 112:=by decide +kernel
  exact zeroAtFast_sound 29 112 hfast

theorem zr29p113:∀ i ∈ List.range 1,ZeroCheckAt 29 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 29 113:=by decide +kernel
  exact zeroAtFast_sound 29 113 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
