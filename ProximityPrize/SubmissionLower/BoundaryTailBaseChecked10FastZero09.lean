import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr10p128:∀ i ∈ List.range 1,ZeroCheckAt 10 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 128:=by decide +kernel
  exact zeroAtFast_sound 10 128 hfast

theorem zr10p129:∀ i ∈ List.range 1,ZeroCheckAt 10 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 129:=by decide +kernel
  exact zeroAtFast_sound 10 129 hfast

theorem zr10p130:∀ i ∈ List.range 1,ZeroCheckAt 10 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 130:=by decide +kernel
  exact zeroAtFast_sound 10 130 hfast

theorem zr10p131:∀ i ∈ List.range 1,ZeroCheckAt 10 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 131:=by decide +kernel
  exact zeroAtFast_sound 10 131 hfast

theorem zr10p132:∀ i ∈ List.range 1,ZeroCheckAt 10 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 132:=by decide +kernel
  exact zeroAtFast_sound 10 132 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
