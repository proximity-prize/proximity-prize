import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr12p128:∀ i ∈ List.range 1,ZeroCheckAt 12 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 128:=by decide +kernel
  exact zeroAtFast_sound 12 128 hfast

theorem zr12p129:∀ i ∈ List.range 1,ZeroCheckAt 12 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 129:=by decide +kernel
  exact zeroAtFast_sound 12 129 hfast

theorem zr12p130:∀ i ∈ List.range 1,ZeroCheckAt 12 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 130:=by decide +kernel
  exact zeroAtFast_sound 12 130 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
