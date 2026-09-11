import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr9p0:∀ i ∈ List.range 1,ZeroCheckAt 9 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 0:=by decide +kernel
  exact zeroAtFast_sound 9 0 hfast

theorem zr9p1:∀ i ∈ List.range 1,ZeroCheckAt 9 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 1:=by decide +kernel
  exact zeroAtFast_sound 9 1 hfast

theorem zr9p2:∀ i ∈ List.range 1,ZeroCheckAt 9 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 2:=by decide +kernel
  exact zeroAtFast_sound 9 2 hfast

theorem zr9p3:∀ i ∈ List.range 1,ZeroCheckAt 9 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 3:=by decide +kernel
  exact zeroAtFast_sound 9 3 hfast

theorem zr9p4:∀ i ∈ List.range 1,ZeroCheckAt 9 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 4:=by decide +kernel
  exact zeroAtFast_sound 9 4 hfast

theorem zr9p5:∀ i ∈ List.range 1,ZeroCheckAt 9 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 5:=by decide +kernel
  exact zeroAtFast_sound 9 5 hfast

theorem zr9p6:∀ i ∈ List.range 1,ZeroCheckAt 9 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 6:=by decide +kernel
  exact zeroAtFast_sound 9 6 hfast

theorem zr9p7:∀ i ∈ List.range 1,ZeroCheckAt 9 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 7:=by decide +kernel
  exact zeroAtFast_sound 9 7 hfast

theorem zr9p8:∀ i ∈ List.range 1,ZeroCheckAt 9 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 8:=by decide +kernel
  exact zeroAtFast_sound 9 8 hfast

theorem zr9p9:∀ i ∈ List.range 1,ZeroCheckAt 9 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 9:=by decide +kernel
  exact zeroAtFast_sound 9 9 hfast

theorem zr9p10:∀ i ∈ List.range 1,ZeroCheckAt 9 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 10:=by decide +kernel
  exact zeroAtFast_sound 9 10 hfast

theorem zr9p11:∀ i ∈ List.range 1,ZeroCheckAt 9 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 11:=by decide +kernel
  exact zeroAtFast_sound 9 11 hfast

theorem zr9p12:∀ i ∈ List.range 1,ZeroCheckAt 9 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 12:=by decide +kernel
  exact zeroAtFast_sound 9 12 hfast

theorem zr9p13:∀ i ∈ List.range 1,ZeroCheckAt 9 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 13:=by decide +kernel
  exact zeroAtFast_sound 9 13 hfast

theorem zr9p14:∀ i ∈ List.range 1,ZeroCheckAt 9 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 14:=by decide +kernel
  exact zeroAtFast_sound 9 14 hfast

theorem zr9p15:∀ i ∈ List.range 1,ZeroCheckAt 9 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 9 15:=by decide +kernel
  exact zeroAtFast_sound 9 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
