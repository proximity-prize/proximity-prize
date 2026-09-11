import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr22p0:∀ i ∈ List.range 1,ZeroCheckAt 22 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 0:=by decide +kernel
  exact zeroAtFast_sound 22 0 hfast

theorem zr22p1:∀ i ∈ List.range 1,ZeroCheckAt 22 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 1:=by decide +kernel
  exact zeroAtFast_sound 22 1 hfast

theorem zr22p2:∀ i ∈ List.range 1,ZeroCheckAt 22 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 2:=by decide +kernel
  exact zeroAtFast_sound 22 2 hfast

theorem zr22p3:∀ i ∈ List.range 1,ZeroCheckAt 22 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 3:=by decide +kernel
  exact zeroAtFast_sound 22 3 hfast

theorem zr22p4:∀ i ∈ List.range 1,ZeroCheckAt 22 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 4:=by decide +kernel
  exact zeroAtFast_sound 22 4 hfast

theorem zr22p5:∀ i ∈ List.range 1,ZeroCheckAt 22 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 5:=by decide +kernel
  exact zeroAtFast_sound 22 5 hfast

theorem zr22p6:∀ i ∈ List.range 1,ZeroCheckAt 22 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 6:=by decide +kernel
  exact zeroAtFast_sound 22 6 hfast

theorem zr22p7:∀ i ∈ List.range 1,ZeroCheckAt 22 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 7:=by decide +kernel
  exact zeroAtFast_sound 22 7 hfast

theorem zr22p8:∀ i ∈ List.range 1,ZeroCheckAt 22 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 8:=by decide +kernel
  exact zeroAtFast_sound 22 8 hfast

theorem zr22p9:∀ i ∈ List.range 1,ZeroCheckAt 22 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 9:=by decide +kernel
  exact zeroAtFast_sound 22 9 hfast

theorem zr22p10:∀ i ∈ List.range 1,ZeroCheckAt 22 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 10:=by decide +kernel
  exact zeroAtFast_sound 22 10 hfast

theorem zr22p11:∀ i ∈ List.range 1,ZeroCheckAt 22 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 11:=by decide +kernel
  exact zeroAtFast_sound 22 11 hfast

theorem zr22p12:∀ i ∈ List.range 1,ZeroCheckAt 22 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 12:=by decide +kernel
  exact zeroAtFast_sound 22 12 hfast

theorem zr22p13:∀ i ∈ List.range 1,ZeroCheckAt 22 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 13:=by decide +kernel
  exact zeroAtFast_sound 22 13 hfast

theorem zr22p14:∀ i ∈ List.range 1,ZeroCheckAt 22 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 14:=by decide +kernel
  exact zeroAtFast_sound 22 14 hfast

theorem zr22p15:∀ i ∈ List.range 1,ZeroCheckAt 22 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 22 15:=by decide +kernel
  exact zeroAtFast_sound 22 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
