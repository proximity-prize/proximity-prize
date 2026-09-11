import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr17p0:∀ i ∈ List.range 1,ZeroCheckAt 17 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 0:=by decide +kernel
  exact zeroAtFast_sound 17 0 hfast

theorem zr17p1:∀ i ∈ List.range 1,ZeroCheckAt 17 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 1:=by decide +kernel
  exact zeroAtFast_sound 17 1 hfast

theorem zr17p2:∀ i ∈ List.range 1,ZeroCheckAt 17 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 2:=by decide +kernel
  exact zeroAtFast_sound 17 2 hfast

theorem zr17p3:∀ i ∈ List.range 1,ZeroCheckAt 17 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 3:=by decide +kernel
  exact zeroAtFast_sound 17 3 hfast

theorem zr17p4:∀ i ∈ List.range 1,ZeroCheckAt 17 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 4:=by decide +kernel
  exact zeroAtFast_sound 17 4 hfast

theorem zr17p5:∀ i ∈ List.range 1,ZeroCheckAt 17 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 5:=by decide +kernel
  exact zeroAtFast_sound 17 5 hfast

theorem zr17p6:∀ i ∈ List.range 1,ZeroCheckAt 17 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 6:=by decide +kernel
  exact zeroAtFast_sound 17 6 hfast

theorem zr17p7:∀ i ∈ List.range 1,ZeroCheckAt 17 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 7:=by decide +kernel
  exact zeroAtFast_sound 17 7 hfast

theorem zr17p8:∀ i ∈ List.range 1,ZeroCheckAt 17 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 8:=by decide +kernel
  exact zeroAtFast_sound 17 8 hfast

theorem zr17p9:∀ i ∈ List.range 1,ZeroCheckAt 17 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 9:=by decide +kernel
  exact zeroAtFast_sound 17 9 hfast

theorem zr17p10:∀ i ∈ List.range 1,ZeroCheckAt 17 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 10:=by decide +kernel
  exact zeroAtFast_sound 17 10 hfast

theorem zr17p11:∀ i ∈ List.range 1,ZeroCheckAt 17 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 11:=by decide +kernel
  exact zeroAtFast_sound 17 11 hfast

theorem zr17p12:∀ i ∈ List.range 1,ZeroCheckAt 17 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 12:=by decide +kernel
  exact zeroAtFast_sound 17 12 hfast

theorem zr17p13:∀ i ∈ List.range 1,ZeroCheckAt 17 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 13:=by decide +kernel
  exact zeroAtFast_sound 17 13 hfast

theorem zr17p14:∀ i ∈ List.range 1,ZeroCheckAt 17 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 14:=by decide +kernel
  exact zeroAtFast_sound 17 14 hfast

theorem zr17p15:∀ i ∈ List.range 1,ZeroCheckAt 17 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 17 15:=by decide +kernel
  exact zeroAtFast_sound 17 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
