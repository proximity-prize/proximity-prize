import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr25p112:∀ i ∈ List.range 1,ZeroCheckAt 25 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 112:=by decide +kernel
  exact zeroAtFast_sound 25 112 hfast

theorem zr25p113:∀ i ∈ List.range 1,ZeroCheckAt 25 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 113:=by decide +kernel
  exact zeroAtFast_sound 25 113 hfast

theorem zr25p114:∀ i ∈ List.range 1,ZeroCheckAt 25 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 114:=by decide +kernel
  exact zeroAtFast_sound 25 114 hfast

theorem zr25p115:∀ i ∈ List.range 1,ZeroCheckAt 25 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 115:=by decide +kernel
  exact zeroAtFast_sound 25 115 hfast

theorem zr25p116:∀ i ∈ List.range 1,ZeroCheckAt 25 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 116:=by decide +kernel
  exact zeroAtFast_sound 25 116 hfast

theorem zr25p117:∀ i ∈ List.range 1,ZeroCheckAt 25 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 117:=by decide +kernel
  exact zeroAtFast_sound 25 117 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
