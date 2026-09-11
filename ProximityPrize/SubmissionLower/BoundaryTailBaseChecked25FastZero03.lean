import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr25p32:∀ i ∈ List.range 1,ZeroCheckAt 25 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 32:=by decide +kernel
  exact zeroAtFast_sound 25 32 hfast

theorem zr25p33:∀ i ∈ List.range 1,ZeroCheckAt 25 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 33:=by decide +kernel
  exact zeroAtFast_sound 25 33 hfast

theorem zr25p34:∀ i ∈ List.range 1,ZeroCheckAt 25 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 34:=by decide +kernel
  exact zeroAtFast_sound 25 34 hfast

theorem zr25p35:∀ i ∈ List.range 1,ZeroCheckAt 25 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 35:=by decide +kernel
  exact zeroAtFast_sound 25 35 hfast

theorem zr25p36:∀ i ∈ List.range 1,ZeroCheckAt 25 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 36:=by decide +kernel
  exact zeroAtFast_sound 25 36 hfast

theorem zr25p37:∀ i ∈ List.range 1,ZeroCheckAt 25 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 37:=by decide +kernel
  exact zeroAtFast_sound 25 37 hfast

theorem zr25p38:∀ i ∈ List.range 1,ZeroCheckAt 25 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 38:=by decide +kernel
  exact zeroAtFast_sound 25 38 hfast

theorem zr25p39:∀ i ∈ List.range 1,ZeroCheckAt 25 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 39:=by decide +kernel
  exact zeroAtFast_sound 25 39 hfast

theorem zr25p40:∀ i ∈ List.range 1,ZeroCheckAt 25 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 40:=by decide +kernel
  exact zeroAtFast_sound 25 40 hfast

theorem zr25p41:∀ i ∈ List.range 1,ZeroCheckAt 25 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 41:=by decide +kernel
  exact zeroAtFast_sound 25 41 hfast

theorem zr25p42:∀ i ∈ List.range 1,ZeroCheckAt 25 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 42:=by decide +kernel
  exact zeroAtFast_sound 25 42 hfast

theorem zr25p43:∀ i ∈ List.range 1,ZeroCheckAt 25 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 43:=by decide +kernel
  exact zeroAtFast_sound 25 43 hfast

theorem zr25p44:∀ i ∈ List.range 1,ZeroCheckAt 25 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 44:=by decide +kernel
  exact zeroAtFast_sound 25 44 hfast

theorem zr25p45:∀ i ∈ List.range 1,ZeroCheckAt 25 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 45:=by decide +kernel
  exact zeroAtFast_sound 25 45 hfast

theorem zr25p46:∀ i ∈ List.range 1,ZeroCheckAt 25 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 46:=by decide +kernel
  exact zeroAtFast_sound 25 46 hfast

theorem zr25p47:∀ i ∈ List.range 1,ZeroCheckAt 25 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 47:=by decide +kernel
  exact zeroAtFast_sound 25 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
