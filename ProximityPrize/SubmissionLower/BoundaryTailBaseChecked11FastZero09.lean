import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr11p128:∀ i ∈ List.range 1,ZeroCheckAt 11 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 11 128:=by decide +kernel
  exact zeroAtFast_sound 11 128 hfast

theorem zr11p129:∀ i ∈ List.range 1,ZeroCheckAt 11 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 11 129:=by decide +kernel
  exact zeroAtFast_sound 11 129 hfast

theorem zr11p130:∀ i ∈ List.range 1,ZeroCheckAt 11 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 11 130:=by decide +kernel
  exact zeroAtFast_sound 11 130 hfast

theorem zr11p131:∀ i ∈ List.range 1,ZeroCheckAt 11 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 11 131:=by decide +kernel
  exact zeroAtFast_sound 11 131 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
