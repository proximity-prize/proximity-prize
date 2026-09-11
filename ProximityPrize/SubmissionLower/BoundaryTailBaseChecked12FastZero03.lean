import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastZero02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr12p32:∀ i ∈ List.range 1,ZeroCheckAt 12 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 32:=by decide +kernel
  exact zeroAtFast_sound 12 32 hfast

theorem zr12p33:∀ i ∈ List.range 1,ZeroCheckAt 12 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 33:=by decide +kernel
  exact zeroAtFast_sound 12 33 hfast

theorem zr12p34:∀ i ∈ List.range 1,ZeroCheckAt 12 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 34:=by decide +kernel
  exact zeroAtFast_sound 12 34 hfast

theorem zr12p35:∀ i ∈ List.range 1,ZeroCheckAt 12 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 35:=by decide +kernel
  exact zeroAtFast_sound 12 35 hfast

theorem zr12p36:∀ i ∈ List.range 1,ZeroCheckAt 12 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 36:=by decide +kernel
  exact zeroAtFast_sound 12 36 hfast

theorem zr12p37:∀ i ∈ List.range 1,ZeroCheckAt 12 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 37:=by decide +kernel
  exact zeroAtFast_sound 12 37 hfast

theorem zr12p38:∀ i ∈ List.range 1,ZeroCheckAt 12 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 38:=by decide +kernel
  exact zeroAtFast_sound 12 38 hfast

theorem zr12p39:∀ i ∈ List.range 1,ZeroCheckAt 12 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 39:=by decide +kernel
  exact zeroAtFast_sound 12 39 hfast

theorem zr12p40:∀ i ∈ List.range 1,ZeroCheckAt 12 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 40:=by decide +kernel
  exact zeroAtFast_sound 12 40 hfast

theorem zr12p41:∀ i ∈ List.range 1,ZeroCheckAt 12 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 41:=by decide +kernel
  exact zeroAtFast_sound 12 41 hfast

theorem zr12p42:∀ i ∈ List.range 1,ZeroCheckAt 12 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 42:=by decide +kernel
  exact zeroAtFast_sound 12 42 hfast

theorem zr12p43:∀ i ∈ List.range 1,ZeroCheckAt 12 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 43:=by decide +kernel
  exact zeroAtFast_sound 12 43 hfast

theorem zr12p44:∀ i ∈ List.range 1,ZeroCheckAt 12 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 44:=by decide +kernel
  exact zeroAtFast_sound 12 44 hfast

theorem zr12p45:∀ i ∈ List.range 1,ZeroCheckAt 12 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 45:=by decide +kernel
  exact zeroAtFast_sound 12 45 hfast

theorem zr12p46:∀ i ∈ List.range 1,ZeroCheckAt 12 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 46:=by decide +kernel
  exact zeroAtFast_sound 12 46 hfast

theorem zr12p47:∀ i ∈ List.range 1,ZeroCheckAt 12 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 12 47:=by decide +kernel
  exact zeroAtFast_sound 12 47 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
