import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr26p112:∀ i ∈ List.range 1,ZeroCheckAt 26 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 26 112:=by decide +kernel
  exact zeroAtFast_sound 26 112 hfast

theorem zr26p113:∀ i ∈ List.range 1,ZeroCheckAt 26 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 26 113:=by decide +kernel
  exact zeroAtFast_sound 26 113 hfast

theorem zr26p114:∀ i ∈ List.range 1,ZeroCheckAt 26 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 26 114:=by decide +kernel
  exact zeroAtFast_sound 26 114 hfast

theorem zr26p115:∀ i ∈ List.range 1,ZeroCheckAt 26 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 26 115:=by decide +kernel
  exact zeroAtFast_sound 26 115 hfast

theorem zr26p116:∀ i ∈ List.range 1,ZeroCheckAt 26 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 26 116:=by decide +kernel
  exact zeroAtFast_sound 26 116 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
