import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr15p0:∀ i ∈ List.range 1,ZeroCheckAt 15 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 0:=by decide +kernel
  exact zeroAtFast_sound 15 0 hfast

theorem zr15p1:∀ i ∈ List.range 1,ZeroCheckAt 15 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 1:=by decide +kernel
  exact zeroAtFast_sound 15 1 hfast

theorem zr15p2:∀ i ∈ List.range 1,ZeroCheckAt 15 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 2:=by decide +kernel
  exact zeroAtFast_sound 15 2 hfast

theorem zr15p3:∀ i ∈ List.range 1,ZeroCheckAt 15 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 3:=by decide +kernel
  exact zeroAtFast_sound 15 3 hfast

theorem zr15p4:∀ i ∈ List.range 1,ZeroCheckAt 15 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 4:=by decide +kernel
  exact zeroAtFast_sound 15 4 hfast

theorem zr15p5:∀ i ∈ List.range 1,ZeroCheckAt 15 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 5:=by decide +kernel
  exact zeroAtFast_sound 15 5 hfast

theorem zr15p6:∀ i ∈ List.range 1,ZeroCheckAt 15 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 6:=by decide +kernel
  exact zeroAtFast_sound 15 6 hfast

theorem zr15p7:∀ i ∈ List.range 1,ZeroCheckAt 15 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 7:=by decide +kernel
  exact zeroAtFast_sound 15 7 hfast

theorem zr15p8:∀ i ∈ List.range 1,ZeroCheckAt 15 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 8:=by decide +kernel
  exact zeroAtFast_sound 15 8 hfast

theorem zr15p9:∀ i ∈ List.range 1,ZeroCheckAt 15 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 9:=by decide +kernel
  exact zeroAtFast_sound 15 9 hfast

theorem zr15p10:∀ i ∈ List.range 1,ZeroCheckAt 15 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 10:=by decide +kernel
  exact zeroAtFast_sound 15 10 hfast

theorem zr15p11:∀ i ∈ List.range 1,ZeroCheckAt 15 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 11:=by decide +kernel
  exact zeroAtFast_sound 15 11 hfast

theorem zr15p12:∀ i ∈ List.range 1,ZeroCheckAt 15 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 12:=by decide +kernel
  exact zeroAtFast_sound 15 12 hfast

theorem zr15p13:∀ i ∈ List.range 1,ZeroCheckAt 15 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 13:=by decide +kernel
  exact zeroAtFast_sound 15 13 hfast

theorem zr15p14:∀ i ∈ List.range 1,ZeroCheckAt 15 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 14:=by decide +kernel
  exact zeroAtFast_sound 15 14 hfast

theorem zr15p15:∀ i ∈ List.range 1,ZeroCheckAt 15 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 15 15:=by decide +kernel
  exact zeroAtFast_sound 15 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
