import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr16p0:∀ i ∈ List.range 1,ZeroCheckAt 16 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 0:=by decide +kernel
  exact zeroAtFast_sound 16 0 hfast

theorem zr16p1:∀ i ∈ List.range 1,ZeroCheckAt 16 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 1:=by decide +kernel
  exact zeroAtFast_sound 16 1 hfast

theorem zr16p2:∀ i ∈ List.range 1,ZeroCheckAt 16 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 2:=by decide +kernel
  exact zeroAtFast_sound 16 2 hfast

theorem zr16p3:∀ i ∈ List.range 1,ZeroCheckAt 16 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 3:=by decide +kernel
  exact zeroAtFast_sound 16 3 hfast

theorem zr16p4:∀ i ∈ List.range 1,ZeroCheckAt 16 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 4:=by decide +kernel
  exact zeroAtFast_sound 16 4 hfast

theorem zr16p5:∀ i ∈ List.range 1,ZeroCheckAt 16 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 5:=by decide +kernel
  exact zeroAtFast_sound 16 5 hfast

theorem zr16p6:∀ i ∈ List.range 1,ZeroCheckAt 16 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 6:=by decide +kernel
  exact zeroAtFast_sound 16 6 hfast

theorem zr16p7:∀ i ∈ List.range 1,ZeroCheckAt 16 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 7:=by decide +kernel
  exact zeroAtFast_sound 16 7 hfast

theorem zr16p8:∀ i ∈ List.range 1,ZeroCheckAt 16 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 8:=by decide +kernel
  exact zeroAtFast_sound 16 8 hfast

theorem zr16p9:∀ i ∈ List.range 1,ZeroCheckAt 16 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 9:=by decide +kernel
  exact zeroAtFast_sound 16 9 hfast

theorem zr16p10:∀ i ∈ List.range 1,ZeroCheckAt 16 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 10:=by decide +kernel
  exact zeroAtFast_sound 16 10 hfast

theorem zr16p11:∀ i ∈ List.range 1,ZeroCheckAt 16 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 11:=by decide +kernel
  exact zeroAtFast_sound 16 11 hfast

theorem zr16p12:∀ i ∈ List.range 1,ZeroCheckAt 16 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 12:=by decide +kernel
  exact zeroAtFast_sound 16 12 hfast

theorem zr16p13:∀ i ∈ List.range 1,ZeroCheckAt 16 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 13:=by decide +kernel
  exact zeroAtFast_sound 16 13 hfast

theorem zr16p14:∀ i ∈ List.range 1,ZeroCheckAt 16 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 14:=by decide +kernel
  exact zeroAtFast_sound 16 14 hfast

theorem zr16p15:∀ i ∈ List.range 1,ZeroCheckAt 16 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 16 15:=by decide +kernel
  exact zeroAtFast_sound 16 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
