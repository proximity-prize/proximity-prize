import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr18p32:∀ i ∈ List.range 1,ZeroCheckAt 18 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 32:=by decide +kernel
  exact zeroAtFast_sound 18 32 hfast

theorem zr18p33:∀ i ∈ List.range 1,ZeroCheckAt 18 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 33:=by decide +kernel
  exact zeroAtFast_sound 18 33 hfast

theorem zr18p34:∀ i ∈ List.range 1,ZeroCheckAt 18 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 34:=by decide +kernel
  exact zeroAtFast_sound 18 34 hfast

theorem zr18p35:∀ i ∈ List.range 1,ZeroCheckAt 18 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 35:=by decide +kernel
  exact zeroAtFast_sound 18 35 hfast

theorem zr18p36:∀ i ∈ List.range 1,ZeroCheckAt 18 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 36:=by decide +kernel
  exact zeroAtFast_sound 18 36 hfast

theorem zr18p37:∀ i ∈ List.range 1,ZeroCheckAt 18 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 37:=by decide +kernel
  exact zeroAtFast_sound 18 37 hfast

theorem zr18p38:∀ i ∈ List.range 1,ZeroCheckAt 18 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 38:=by decide +kernel
  exact zeroAtFast_sound 18 38 hfast

theorem zr18p39:∀ i ∈ List.range 1,ZeroCheckAt 18 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 39:=by decide +kernel
  exact zeroAtFast_sound 18 39 hfast

theorem zr18p40:∀ i ∈ List.range 1,ZeroCheckAt 18 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 40:=by decide +kernel
  exact zeroAtFast_sound 18 40 hfast

theorem zr18p41:∀ i ∈ List.range 1,ZeroCheckAt 18 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 41:=by decide +kernel
  exact zeroAtFast_sound 18 41 hfast

theorem zr18p42:∀ i ∈ List.range 1,ZeroCheckAt 18 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 42:=by decide +kernel
  exact zeroAtFast_sound 18 42 hfast

theorem zr18p43:∀ i ∈ List.range 1,ZeroCheckAt 18 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 43:=by decide +kernel
  exact zeroAtFast_sound 18 43 hfast

theorem zr18p44:∀ i ∈ List.range 1,ZeroCheckAt 18 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 44:=by decide +kernel
  exact zeroAtFast_sound 18 44 hfast

theorem zr18p45:∀ i ∈ List.range 1,ZeroCheckAt 18 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 45:=by decide +kernel
  exact zeroAtFast_sound 18 45 hfast

theorem zr18p46:∀ i ∈ List.range 1,ZeroCheckAt 18 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 46:=by decide +kernel
  exact zeroAtFast_sound 18 46 hfast

theorem zr18p47:∀ i ∈ List.range 1,ZeroCheckAt 18 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 18 47:=by decide +kernel
  exact zeroAtFast_sound 18 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
