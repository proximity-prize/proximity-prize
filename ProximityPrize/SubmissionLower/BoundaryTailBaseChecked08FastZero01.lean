import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr8p0:∀ i ∈ List.range 1,ZeroCheckAt 8 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 0:=by decide +kernel
  exact zeroAtFast_sound 8 0 hfast

theorem zr8p1:∀ i ∈ List.range 1,ZeroCheckAt 8 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 1:=by decide +kernel
  exact zeroAtFast_sound 8 1 hfast

theorem zr8p2:∀ i ∈ List.range 1,ZeroCheckAt 8 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 2:=by decide +kernel
  exact zeroAtFast_sound 8 2 hfast

theorem zr8p3:∀ i ∈ List.range 1,ZeroCheckAt 8 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 3:=by decide +kernel
  exact zeroAtFast_sound 8 3 hfast

theorem zr8p4:∀ i ∈ List.range 1,ZeroCheckAt 8 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 4:=by decide +kernel
  exact zeroAtFast_sound 8 4 hfast

theorem zr8p5:∀ i ∈ List.range 1,ZeroCheckAt 8 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 5:=by decide +kernel
  exact zeroAtFast_sound 8 5 hfast

theorem zr8p6:∀ i ∈ List.range 1,ZeroCheckAt 8 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 6:=by decide +kernel
  exact zeroAtFast_sound 8 6 hfast

theorem zr8p7:∀ i ∈ List.range 1,ZeroCheckAt 8 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 7:=by decide +kernel
  exact zeroAtFast_sound 8 7 hfast

theorem zr8p8:∀ i ∈ List.range 1,ZeroCheckAt 8 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 8:=by decide +kernel
  exact zeroAtFast_sound 8 8 hfast

theorem zr8p9:∀ i ∈ List.range 1,ZeroCheckAt 8 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 9:=by decide +kernel
  exact zeroAtFast_sound 8 9 hfast

theorem zr8p10:∀ i ∈ List.range 1,ZeroCheckAt 8 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 10:=by decide +kernel
  exact zeroAtFast_sound 8 10 hfast

theorem zr8p11:∀ i ∈ List.range 1,ZeroCheckAt 8 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 11:=by decide +kernel
  exact zeroAtFast_sound 8 11 hfast

theorem zr8p12:∀ i ∈ List.range 1,ZeroCheckAt 8 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 12:=by decide +kernel
  exact zeroAtFast_sound 8 12 hfast

theorem zr8p13:∀ i ∈ List.range 1,ZeroCheckAt 8 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 13:=by decide +kernel
  exact zeroAtFast_sound 8 13 hfast

theorem zr8p14:∀ i ∈ List.range 1,ZeroCheckAt 8 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 14:=by decide +kernel
  exact zeroAtFast_sound 8 14 hfast

theorem zr8p15:∀ i ∈ List.range 1,ZeroCheckAt 8 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 8 15:=by decide +kernel
  exact zeroAtFast_sound 8 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
