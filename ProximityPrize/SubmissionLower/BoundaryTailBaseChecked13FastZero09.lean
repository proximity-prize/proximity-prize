import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr13p128:∀ i ∈ List.range 1,ZeroCheckAt 13 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 13 128:=by decide +kernel
  exact zeroAtFast_sound 13 128 hfast

theorem zr13p129:∀ i ∈ List.range 1,ZeroCheckAt 13 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 13 129:=by decide +kernel
  exact zeroAtFast_sound 13 129 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
