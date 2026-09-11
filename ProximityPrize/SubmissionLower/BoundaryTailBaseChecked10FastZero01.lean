import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr10p0:∀ i ∈ List.range 1,ZeroCheckAt 10 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 0:=by decide +kernel
  exact zeroAtFast_sound 10 0 hfast

theorem zr10p1:∀ i ∈ List.range 1,ZeroCheckAt 10 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 1:=by decide +kernel
  exact zeroAtFast_sound 10 1 hfast

theorem zr10p2:∀ i ∈ List.range 1,ZeroCheckAt 10 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 2:=by decide +kernel
  exact zeroAtFast_sound 10 2 hfast

theorem zr10p3:∀ i ∈ List.range 1,ZeroCheckAt 10 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 3:=by decide +kernel
  exact zeroAtFast_sound 10 3 hfast

theorem zr10p4:∀ i ∈ List.range 1,ZeroCheckAt 10 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 4:=by decide +kernel
  exact zeroAtFast_sound 10 4 hfast

theorem zr10p5:∀ i ∈ List.range 1,ZeroCheckAt 10 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 5:=by decide +kernel
  exact zeroAtFast_sound 10 5 hfast

theorem zr10p6:∀ i ∈ List.range 1,ZeroCheckAt 10 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 6:=by decide +kernel
  exact zeroAtFast_sound 10 6 hfast

theorem zr10p7:∀ i ∈ List.range 1,ZeroCheckAt 10 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 7:=by decide +kernel
  exact zeroAtFast_sound 10 7 hfast

theorem zr10p8:∀ i ∈ List.range 1,ZeroCheckAt 10 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 8:=by decide +kernel
  exact zeroAtFast_sound 10 8 hfast

theorem zr10p9:∀ i ∈ List.range 1,ZeroCheckAt 10 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 9:=by decide +kernel
  exact zeroAtFast_sound 10 9 hfast

theorem zr10p10:∀ i ∈ List.range 1,ZeroCheckAt 10 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 10:=by decide +kernel
  exact zeroAtFast_sound 10 10 hfast

theorem zr10p11:∀ i ∈ List.range 1,ZeroCheckAt 10 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 11:=by decide +kernel
  exact zeroAtFast_sound 10 11 hfast

theorem zr10p12:∀ i ∈ List.range 1,ZeroCheckAt 10 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 12:=by decide +kernel
  exact zeroAtFast_sound 10 12 hfast

theorem zr10p13:∀ i ∈ List.range 1,ZeroCheckAt 10 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 13:=by decide +kernel
  exact zeroAtFast_sound 10 13 hfast

theorem zr10p14:∀ i ∈ List.range 1,ZeroCheckAt 10 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 14:=by decide +kernel
  exact zeroAtFast_sound 10 14 hfast

theorem zr10p15:∀ i ∈ List.range 1,ZeroCheckAt 10 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 10 15:=by decide +kernel
  exact zeroAtFast_sound 10 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
