import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr16p112:∀ i ∈ List.range 1,ZeroCheckAt 16 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 112:=by decide +kernel
  exact zeroAtFast_sound 16 112 hfast

theorem zr16p113:∀ i ∈ List.range 1,ZeroCheckAt 16 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 113:=by decide +kernel
  exact zeroAtFast_sound 16 113 hfast

theorem zr16p114:∀ i ∈ List.range 1,ZeroCheckAt 16 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 114:=by decide +kernel
  exact zeroAtFast_sound 16 114 hfast

theorem zr16p115:∀ i ∈ List.range 1,ZeroCheckAt 16 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 115:=by decide +kernel
  exact zeroAtFast_sound 16 115 hfast

theorem zr16p116:∀ i ∈ List.range 1,ZeroCheckAt 16 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 116:=by decide +kernel
  exact zeroAtFast_sound 16 116 hfast

theorem zr16p117:∀ i ∈ List.range 1,ZeroCheckAt 16 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 117:=by decide +kernel
  exact zeroAtFast_sound 16 117 hfast

theorem zr16p118:∀ i ∈ List.range 1,ZeroCheckAt 16 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 118:=by decide +kernel
  exact zeroAtFast_sound 16 118 hfast

theorem zr16p119:∀ i ∈ List.range 1,ZeroCheckAt 16 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 119:=by decide +kernel
  exact zeroAtFast_sound 16 119 hfast

theorem zr16p120:∀ i ∈ List.range 1,ZeroCheckAt 16 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 120:=by decide +kernel
  exact zeroAtFast_sound 16 120 hfast

theorem zr16p121:∀ i ∈ List.range 1,ZeroCheckAt 16 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 121:=by decide +kernel
  exact zeroAtFast_sound 16 121 hfast

theorem zr16p122:∀ i ∈ List.range 1,ZeroCheckAt 16 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 122:=by decide +kernel
  exact zeroAtFast_sound 16 122 hfast

theorem zr16p123:∀ i ∈ List.range 1,ZeroCheckAt 16 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 123:=by decide +kernel
  exact zeroAtFast_sound 16 123 hfast

theorem zr16p124:∀ i ∈ List.range 1,ZeroCheckAt 16 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 124:=by decide +kernel
  exact zeroAtFast_sound 16 124 hfast

theorem zr16p125:∀ i ∈ List.range 1,ZeroCheckAt 16 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 125:=by decide +kernel
  exact zeroAtFast_sound 16 125 hfast

theorem zr16p126:∀ i ∈ List.range 1,ZeroCheckAt 16 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 126:=by decide +kernel
  exact zeroAtFast_sound 16 126 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
