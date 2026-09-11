import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr25p0:∀ i ∈ List.range 1,ZeroCheckAt 25 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 0:=by decide +kernel
  exact zeroAtFast_sound 25 0 hfast

theorem zr25p1:∀ i ∈ List.range 1,ZeroCheckAt 25 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 1:=by decide +kernel
  exact zeroAtFast_sound 25 1 hfast

theorem zr25p2:∀ i ∈ List.range 1,ZeroCheckAt 25 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 2:=by decide +kernel
  exact zeroAtFast_sound 25 2 hfast

theorem zr25p3:∀ i ∈ List.range 1,ZeroCheckAt 25 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 3:=by decide +kernel
  exact zeroAtFast_sound 25 3 hfast

theorem zr25p4:∀ i ∈ List.range 1,ZeroCheckAt 25 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 4:=by decide +kernel
  exact zeroAtFast_sound 25 4 hfast

theorem zr25p5:∀ i ∈ List.range 1,ZeroCheckAt 25 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 5:=by decide +kernel
  exact zeroAtFast_sound 25 5 hfast

theorem zr25p6:∀ i ∈ List.range 1,ZeroCheckAt 25 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 6:=by decide +kernel
  exact zeroAtFast_sound 25 6 hfast

theorem zr25p7:∀ i ∈ List.range 1,ZeroCheckAt 25 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 7:=by decide +kernel
  exact zeroAtFast_sound 25 7 hfast

theorem zr25p8:∀ i ∈ List.range 1,ZeroCheckAt 25 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 8:=by decide +kernel
  exact zeroAtFast_sound 25 8 hfast

theorem zr25p9:∀ i ∈ List.range 1,ZeroCheckAt 25 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 9:=by decide +kernel
  exact zeroAtFast_sound 25 9 hfast

theorem zr25p10:∀ i ∈ List.range 1,ZeroCheckAt 25 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 10:=by decide +kernel
  exact zeroAtFast_sound 25 10 hfast

theorem zr25p11:∀ i ∈ List.range 1,ZeroCheckAt 25 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 11:=by decide +kernel
  exact zeroAtFast_sound 25 11 hfast

theorem zr25p12:∀ i ∈ List.range 1,ZeroCheckAt 25 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 12:=by decide +kernel
  exact zeroAtFast_sound 25 12 hfast

theorem zr25p13:∀ i ∈ List.range 1,ZeroCheckAt 25 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 13:=by decide +kernel
  exact zeroAtFast_sound 25 13 hfast

theorem zr25p14:∀ i ∈ List.range 1,ZeroCheckAt 25 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 14:=by decide +kernel
  exact zeroAtFast_sound 25 14 hfast

theorem zr25p15:∀ i ∈ List.range 1,ZeroCheckAt 25 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 25 15:=by decide +kernel
  exact zeroAtFast_sound 25 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
