import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr22p112:∀ i ∈ List.range 1,ZeroCheckAt 22 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 112:=by decide +kernel
  exact zeroAtFast_sound 22 112 hfast

theorem zr22p113:∀ i ∈ List.range 1,ZeroCheckAt 22 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 113:=by decide +kernel
  exact zeroAtFast_sound 22 113 hfast

theorem zr22p114:∀ i ∈ List.range 1,ZeroCheckAt 22 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 114:=by decide +kernel
  exact zeroAtFast_sound 22 114 hfast

theorem zr22p115:∀ i ∈ List.range 1,ZeroCheckAt 22 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 115:=by decide +kernel
  exact zeroAtFast_sound 22 115 hfast

theorem zr22p116:∀ i ∈ List.range 1,ZeroCheckAt 22 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 116:=by decide +kernel
  exact zeroAtFast_sound 22 116 hfast

theorem zr22p117:∀ i ∈ List.range 1,ZeroCheckAt 22 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 117:=by decide +kernel
  exact zeroAtFast_sound 22 117 hfast

theorem zr22p118:∀ i ∈ List.range 1,ZeroCheckAt 22 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 118:=by decide +kernel
  exact zeroAtFast_sound 22 118 hfast

theorem zr22p119:∀ i ∈ List.range 1,ZeroCheckAt 22 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 119:=by decide +kernel
  exact zeroAtFast_sound 22 119 hfast

theorem zr22p120:∀ i ∈ List.range 1,ZeroCheckAt 22 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 120:=by decide +kernel
  exact zeroAtFast_sound 22 120 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
