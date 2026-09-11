import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr19p112:∀ i ∈ List.range 1,ZeroCheckAt 19 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 112:=by decide +kernel
  exact zeroAtFast_sound 19 112 hfast

theorem zr19p113:∀ i ∈ List.range 1,ZeroCheckAt 19 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 113:=by decide +kernel
  exact zeroAtFast_sound 19 113 hfast

theorem zr19p114:∀ i ∈ List.range 1,ZeroCheckAt 19 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 114:=by decide +kernel
  exact zeroAtFast_sound 19 114 hfast

theorem zr19p115:∀ i ∈ List.range 1,ZeroCheckAt 19 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 115:=by decide +kernel
  exact zeroAtFast_sound 19 115 hfast

theorem zr19p116:∀ i ∈ List.range 1,ZeroCheckAt 19 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 116:=by decide +kernel
  exact zeroAtFast_sound 19 116 hfast

theorem zr19p117:∀ i ∈ List.range 1,ZeroCheckAt 19 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 117:=by decide +kernel
  exact zeroAtFast_sound 19 117 hfast

theorem zr19p118:∀ i ∈ List.range 1,ZeroCheckAt 19 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 118:=by decide +kernel
  exact zeroAtFast_sound 19 118 hfast

theorem zr19p119:∀ i ∈ List.range 1,ZeroCheckAt 19 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 119:=by decide +kernel
  exact zeroAtFast_sound 19 119 hfast

theorem zr19p120:∀ i ∈ List.range 1,ZeroCheckAt 19 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 120:=by decide +kernel
  exact zeroAtFast_sound 19 120 hfast

theorem zr19p121:∀ i ∈ List.range 1,ZeroCheckAt 19 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 121:=by decide +kernel
  exact zeroAtFast_sound 19 121 hfast

theorem zr19p122:∀ i ∈ List.range 1,ZeroCheckAt 19 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 122:=by decide +kernel
  exact zeroAtFast_sound 19 122 hfast

theorem zr19p123:∀ i ∈ List.range 1,ZeroCheckAt 19 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 19 123:=by decide +kernel
  exact zeroAtFast_sound 19 123 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
