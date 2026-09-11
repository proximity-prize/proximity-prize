import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr10p32:∀ i ∈ List.range 1,ZeroCheckAt 10 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 32:=by decide +kernel
  exact zeroAtFast_sound 10 32 hfast

theorem zr10p33:∀ i ∈ List.range 1,ZeroCheckAt 10 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 33:=by decide +kernel
  exact zeroAtFast_sound 10 33 hfast

theorem zr10p34:∀ i ∈ List.range 1,ZeroCheckAt 10 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 34:=by decide +kernel
  exact zeroAtFast_sound 10 34 hfast

theorem zr10p35:∀ i ∈ List.range 1,ZeroCheckAt 10 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 35:=by decide +kernel
  exact zeroAtFast_sound 10 35 hfast

theorem zr10p36:∀ i ∈ List.range 1,ZeroCheckAt 10 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 36:=by decide +kernel
  exact zeroAtFast_sound 10 36 hfast

theorem zr10p37:∀ i ∈ List.range 1,ZeroCheckAt 10 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 37:=by decide +kernel
  exact zeroAtFast_sound 10 37 hfast

theorem zr10p38:∀ i ∈ List.range 1,ZeroCheckAt 10 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 38:=by decide +kernel
  exact zeroAtFast_sound 10 38 hfast

theorem zr10p39:∀ i ∈ List.range 1,ZeroCheckAt 10 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 39:=by decide +kernel
  exact zeroAtFast_sound 10 39 hfast

theorem zr10p40:∀ i ∈ List.range 1,ZeroCheckAt 10 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 40:=by decide +kernel
  exact zeroAtFast_sound 10 40 hfast

theorem zr10p41:∀ i ∈ List.range 1,ZeroCheckAt 10 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 41:=by decide +kernel
  exact zeroAtFast_sound 10 41 hfast

theorem zr10p42:∀ i ∈ List.range 1,ZeroCheckAt 10 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 42:=by decide +kernel
  exact zeroAtFast_sound 10 42 hfast

theorem zr10p43:∀ i ∈ List.range 1,ZeroCheckAt 10 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 43:=by decide +kernel
  exact zeroAtFast_sound 10 43 hfast

theorem zr10p44:∀ i ∈ List.range 1,ZeroCheckAt 10 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 44:=by decide +kernel
  exact zeroAtFast_sound 10 44 hfast

theorem zr10p45:∀ i ∈ List.range 1,ZeroCheckAt 10 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 45:=by decide +kernel
  exact zeroAtFast_sound 10 45 hfast

theorem zr10p46:∀ i ∈ List.range 1,ZeroCheckAt 10 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 46:=by decide +kernel
  exact zeroAtFast_sound 10 46 hfast

theorem zr10p47:∀ i ∈ List.range 1,ZeroCheckAt 10 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 47:=by decide +kernel
  exact zeroAtFast_sound 10 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
