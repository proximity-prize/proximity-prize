import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr21p112:∀ i ∈ List.range 1,ZeroCheckAt 21 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 112:=by decide +kernel
  exact zeroAtFast_sound 21 112 hfast

theorem zr21p113:∀ i ∈ List.range 1,ZeroCheckAt 21 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 113:=by decide +kernel
  exact zeroAtFast_sound 21 113 hfast

theorem zr21p114:∀ i ∈ List.range 1,ZeroCheckAt 21 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 114:=by decide +kernel
  exact zeroAtFast_sound 21 114 hfast

theorem zr21p115:∀ i ∈ List.range 1,ZeroCheckAt 21 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 115:=by decide +kernel
  exact zeroAtFast_sound 21 115 hfast

theorem zr21p116:∀ i ∈ List.range 1,ZeroCheckAt 21 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 116:=by decide +kernel
  exact zeroAtFast_sound 21 116 hfast

theorem zr21p117:∀ i ∈ List.range 1,ZeroCheckAt 21 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 117:=by decide +kernel
  exact zeroAtFast_sound 21 117 hfast

theorem zr21p118:∀ i ∈ List.range 1,ZeroCheckAt 21 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 118:=by decide +kernel
  exact zeroAtFast_sound 21 118 hfast

theorem zr21p119:∀ i ∈ List.range 1,ZeroCheckAt 21 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 119:=by decide +kernel
  exact zeroAtFast_sound 21 119 hfast

theorem zr21p120:∀ i ∈ List.range 1,ZeroCheckAt 21 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 120:=by decide +kernel
  exact zeroAtFast_sound 21 120 hfast

theorem zr21p121:∀ i ∈ List.range 1,ZeroCheckAt 21 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 21 121:=by decide +kernel
  exact zeroAtFast_sound 21 121 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
