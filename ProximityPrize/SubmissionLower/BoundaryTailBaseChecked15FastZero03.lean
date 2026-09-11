import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr15p32:∀ i ∈ List.range 1,ZeroCheckAt 15 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 32:=by decide +kernel
  exact zeroAtFast_sound 15 32 hfast

theorem zr15p33:∀ i ∈ List.range 1,ZeroCheckAt 15 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 33:=by decide +kernel
  exact zeroAtFast_sound 15 33 hfast

theorem zr15p34:∀ i ∈ List.range 1,ZeroCheckAt 15 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 34:=by decide +kernel
  exact zeroAtFast_sound 15 34 hfast

theorem zr15p35:∀ i ∈ List.range 1,ZeroCheckAt 15 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 35:=by decide +kernel
  exact zeroAtFast_sound 15 35 hfast

theorem zr15p36:∀ i ∈ List.range 1,ZeroCheckAt 15 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 36:=by decide +kernel
  exact zeroAtFast_sound 15 36 hfast

theorem zr15p37:∀ i ∈ List.range 1,ZeroCheckAt 15 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 37:=by decide +kernel
  exact zeroAtFast_sound 15 37 hfast

theorem zr15p38:∀ i ∈ List.range 1,ZeroCheckAt 15 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 38:=by decide +kernel
  exact zeroAtFast_sound 15 38 hfast

theorem zr15p39:∀ i ∈ List.range 1,ZeroCheckAt 15 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 39:=by decide +kernel
  exact zeroAtFast_sound 15 39 hfast

theorem zr15p40:∀ i ∈ List.range 1,ZeroCheckAt 15 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 40:=by decide +kernel
  exact zeroAtFast_sound 15 40 hfast

theorem zr15p41:∀ i ∈ List.range 1,ZeroCheckAt 15 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 41:=by decide +kernel
  exact zeroAtFast_sound 15 41 hfast

theorem zr15p42:∀ i ∈ List.range 1,ZeroCheckAt 15 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 42:=by decide +kernel
  exact zeroAtFast_sound 15 42 hfast

theorem zr15p43:∀ i ∈ List.range 1,ZeroCheckAt 15 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 43:=by decide +kernel
  exact zeroAtFast_sound 15 43 hfast

theorem zr15p44:∀ i ∈ List.range 1,ZeroCheckAt 15 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 44:=by decide +kernel
  exact zeroAtFast_sound 15 44 hfast

theorem zr15p45:∀ i ∈ List.range 1,ZeroCheckAt 15 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 45:=by decide +kernel
  exact zeroAtFast_sound 15 45 hfast

theorem zr15p46:∀ i ∈ List.range 1,ZeroCheckAt 15 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 46:=by decide +kernel
  exact zeroAtFast_sound 15 46 hfast

theorem zr15p47:∀ i ∈ List.range 1,ZeroCheckAt 15 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 47:=by decide +kernel
  exact zeroAtFast_sound 15 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
