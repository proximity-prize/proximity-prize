import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr23p112:∀ i ∈ List.range 1,ZeroCheckAt 23 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 112:=by decide +kernel
  exact zeroAtFast_sound 23 112 hfast

theorem zr23p113:∀ i ∈ List.range 1,ZeroCheckAt 23 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 113:=by decide +kernel
  exact zeroAtFast_sound 23 113 hfast

theorem zr23p114:∀ i ∈ List.range 1,ZeroCheckAt 23 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 114:=by decide +kernel
  exact zeroAtFast_sound 23 114 hfast

theorem zr23p115:∀ i ∈ List.range 1,ZeroCheckAt 23 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 115:=by decide +kernel
  exact zeroAtFast_sound 23 115 hfast

theorem zr23p116:∀ i ∈ List.range 1,ZeroCheckAt 23 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 116:=by decide +kernel
  exact zeroAtFast_sound 23 116 hfast

theorem zr23p117:∀ i ∈ List.range 1,ZeroCheckAt 23 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 117:=by decide +kernel
  exact zeroAtFast_sound 23 117 hfast

theorem zr23p118:∀ i ∈ List.range 1,ZeroCheckAt 23 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 118:=by decide +kernel
  exact zeroAtFast_sound 23 118 hfast

theorem zr23p119:∀ i ∈ List.range 1,ZeroCheckAt 23 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 119:=by decide +kernel
  exact zeroAtFast_sound 23 119 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
