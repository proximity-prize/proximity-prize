import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr28p112:∀ i ∈ List.range 1,ZeroCheckAt 28 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 28 112:=by decide +kernel
  exact zeroAtFast_sound 28 112 hfast

theorem zr28p113:∀ i ∈ List.range 1,ZeroCheckAt 28 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 28 113:=by decide +kernel
  exact zeroAtFast_sound 28 113 hfast

theorem zr28p114:∀ i ∈ List.range 1,ZeroCheckAt 28 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 28 114:=by decide +kernel
  exact zeroAtFast_sound 28 114 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
