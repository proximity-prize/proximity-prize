import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr20p112:∀ i ∈ List.range 1,ZeroCheckAt 20 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 112:=by decide +kernel
  exact zeroAtFast_sound 20 112 hfast

theorem zr20p113:∀ i ∈ List.range 1,ZeroCheckAt 20 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 113:=by decide +kernel
  exact zeroAtFast_sound 20 113 hfast

theorem zr20p114:∀ i ∈ List.range 1,ZeroCheckAt 20 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 114:=by decide +kernel
  exact zeroAtFast_sound 20 114 hfast

theorem zr20p115:∀ i ∈ List.range 1,ZeroCheckAt 20 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 115:=by decide +kernel
  exact zeroAtFast_sound 20 115 hfast

theorem zr20p116:∀ i ∈ List.range 1,ZeroCheckAt 20 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 116:=by decide +kernel
  exact zeroAtFast_sound 20 116 hfast

theorem zr20p117:∀ i ∈ List.range 1,ZeroCheckAt 20 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 117:=by decide +kernel
  exact zeroAtFast_sound 20 117 hfast

theorem zr20p118:∀ i ∈ List.range 1,ZeroCheckAt 20 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 118:=by decide +kernel
  exact zeroAtFast_sound 20 118 hfast

theorem zr20p119:∀ i ∈ List.range 1,ZeroCheckAt 20 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 119:=by decide +kernel
  exact zeroAtFast_sound 20 119 hfast

theorem zr20p120:∀ i ∈ List.range 1,ZeroCheckAt 20 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 120:=by decide +kernel
  exact zeroAtFast_sound 20 120 hfast

theorem zr20p121:∀ i ∈ List.range 1,ZeroCheckAt 20 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 121:=by decide +kernel
  exact zeroAtFast_sound 20 121 hfast

theorem zr20p122:∀ i ∈ List.range 1,ZeroCheckAt 20 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 122:=by decide +kernel
  exact zeroAtFast_sound 20 122 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
