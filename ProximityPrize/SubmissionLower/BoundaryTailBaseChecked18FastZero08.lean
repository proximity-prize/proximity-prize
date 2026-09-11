import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr18p112:∀ i ∈ List.range 1,ZeroCheckAt 18 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 112:=by decide +kernel
  exact zeroAtFast_sound 18 112 hfast

theorem zr18p113:∀ i ∈ List.range 1,ZeroCheckAt 18 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 113:=by decide +kernel
  exact zeroAtFast_sound 18 113 hfast

theorem zr18p114:∀ i ∈ List.range 1,ZeroCheckAt 18 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 114:=by decide +kernel
  exact zeroAtFast_sound 18 114 hfast

theorem zr18p115:∀ i ∈ List.range 1,ZeroCheckAt 18 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 115:=by decide +kernel
  exact zeroAtFast_sound 18 115 hfast

theorem zr18p116:∀ i ∈ List.range 1,ZeroCheckAt 18 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 116:=by decide +kernel
  exact zeroAtFast_sound 18 116 hfast

theorem zr18p117:∀ i ∈ List.range 1,ZeroCheckAt 18 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 117:=by decide +kernel
  exact zeroAtFast_sound 18 117 hfast

theorem zr18p118:∀ i ∈ List.range 1,ZeroCheckAt 18 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 118:=by decide +kernel
  exact zeroAtFast_sound 18 118 hfast

theorem zr18p119:∀ i ∈ List.range 1,ZeroCheckAt 18 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 119:=by decide +kernel
  exact zeroAtFast_sound 18 119 hfast

theorem zr18p120:∀ i ∈ List.range 1,ZeroCheckAt 18 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 120:=by decide +kernel
  exact zeroAtFast_sound 18 120 hfast

theorem zr18p121:∀ i ∈ List.range 1,ZeroCheckAt 18 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 121:=by decide +kernel
  exact zeroAtFast_sound 18 121 hfast

theorem zr18p122:∀ i ∈ List.range 1,ZeroCheckAt 18 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 122:=by decide +kernel
  exact zeroAtFast_sound 18 122 hfast

theorem zr18p123:∀ i ∈ List.range 1,ZeroCheckAt 18 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 123:=by decide +kernel
  exact zeroAtFast_sound 18 123 hfast

theorem zr18p124:∀ i ∈ List.range 1,ZeroCheckAt 18 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 124:=by decide +kernel
  exact zeroAtFast_sound 18 124 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
