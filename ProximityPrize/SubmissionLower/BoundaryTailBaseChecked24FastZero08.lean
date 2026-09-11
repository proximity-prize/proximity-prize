import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr24p112:∀ i ∈ List.range 1,ZeroCheckAt 24 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 24 112:=by decide +kernel
  exact zeroAtFast_sound 24 112 hfast

theorem zr24p113:∀ i ∈ List.range 1,ZeroCheckAt 24 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 24 113:=by decide +kernel
  exact zeroAtFast_sound 24 113 hfast

theorem zr24p114:∀ i ∈ List.range 1,ZeroCheckAt 24 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 24 114:=by decide +kernel
  exact zeroAtFast_sound 24 114 hfast

theorem zr24p115:∀ i ∈ List.range 1,ZeroCheckAt 24 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 24 115:=by decide +kernel
  exact zeroAtFast_sound 24 115 hfast

theorem zr24p116:∀ i ∈ List.range 1,ZeroCheckAt 24 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 24 116:=by decide +kernel
  exact zeroAtFast_sound 24 116 hfast

theorem zr24p117:∀ i ∈ List.range 1,ZeroCheckAt 24 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 24 117:=by decide +kernel
  exact zeroAtFast_sound 24 117 hfast

theorem zr24p118:∀ i ∈ List.range 1,ZeroCheckAt 24 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 24 118:=by decide +kernel
  exact zeroAtFast_sound 24 118 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
