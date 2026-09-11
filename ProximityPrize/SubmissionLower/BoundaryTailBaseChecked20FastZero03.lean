import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr20p32:∀ i ∈ List.range 1,ZeroCheckAt 20 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 32:=by decide +kernel
  exact zeroAtFast_sound 20 32 hfast

theorem zr20p33:∀ i ∈ List.range 1,ZeroCheckAt 20 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 33:=by decide +kernel
  exact zeroAtFast_sound 20 33 hfast

theorem zr20p34:∀ i ∈ List.range 1,ZeroCheckAt 20 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 34:=by decide +kernel
  exact zeroAtFast_sound 20 34 hfast

theorem zr20p35:∀ i ∈ List.range 1,ZeroCheckAt 20 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 35:=by decide +kernel
  exact zeroAtFast_sound 20 35 hfast

theorem zr20p36:∀ i ∈ List.range 1,ZeroCheckAt 20 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 36:=by decide +kernel
  exact zeroAtFast_sound 20 36 hfast

theorem zr20p37:∀ i ∈ List.range 1,ZeroCheckAt 20 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 37:=by decide +kernel
  exact zeroAtFast_sound 20 37 hfast

theorem zr20p38:∀ i ∈ List.range 1,ZeroCheckAt 20 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 38:=by decide +kernel
  exact zeroAtFast_sound 20 38 hfast

theorem zr20p39:∀ i ∈ List.range 1,ZeroCheckAt 20 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 39:=by decide +kernel
  exact zeroAtFast_sound 20 39 hfast

theorem zr20p40:∀ i ∈ List.range 1,ZeroCheckAt 20 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 40:=by decide +kernel
  exact zeroAtFast_sound 20 40 hfast

theorem zr20p41:∀ i ∈ List.range 1,ZeroCheckAt 20 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 41:=by decide +kernel
  exact zeroAtFast_sound 20 41 hfast

theorem zr20p42:∀ i ∈ List.range 1,ZeroCheckAt 20 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 42:=by decide +kernel
  exact zeroAtFast_sound 20 42 hfast

theorem zr20p43:∀ i ∈ List.range 1,ZeroCheckAt 20 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 43:=by decide +kernel
  exact zeroAtFast_sound 20 43 hfast

theorem zr20p44:∀ i ∈ List.range 1,ZeroCheckAt 20 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 44:=by decide +kernel
  exact zeroAtFast_sound 20 44 hfast

theorem zr20p45:∀ i ∈ List.range 1,ZeroCheckAt 20 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 45:=by decide +kernel
  exact zeroAtFast_sound 20 45 hfast

theorem zr20p46:∀ i ∈ List.range 1,ZeroCheckAt 20 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 46:=by decide +kernel
  exact zeroAtFast_sound 20 46 hfast

theorem zr20p47:∀ i ∈ List.range 1,ZeroCheckAt 20 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 47:=by decide +kernel
  exact zeroAtFast_sound 20 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
