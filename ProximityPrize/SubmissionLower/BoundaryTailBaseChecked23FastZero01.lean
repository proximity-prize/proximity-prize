import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr23p0:∀ i ∈ List.range 1,ZeroCheckAt 23 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 0:=by decide +kernel
  exact zeroAtFast_sound 23 0 hfast

theorem zr23p1:∀ i ∈ List.range 1,ZeroCheckAt 23 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 1:=by decide +kernel
  exact zeroAtFast_sound 23 1 hfast

theorem zr23p2:∀ i ∈ List.range 1,ZeroCheckAt 23 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 2:=by decide +kernel
  exact zeroAtFast_sound 23 2 hfast

theorem zr23p3:∀ i ∈ List.range 1,ZeroCheckAt 23 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 3:=by decide +kernel
  exact zeroAtFast_sound 23 3 hfast

theorem zr23p4:∀ i ∈ List.range 1,ZeroCheckAt 23 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 4:=by decide +kernel
  exact zeroAtFast_sound 23 4 hfast

theorem zr23p5:∀ i ∈ List.range 1,ZeroCheckAt 23 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 5:=by decide +kernel
  exact zeroAtFast_sound 23 5 hfast

theorem zr23p6:∀ i ∈ List.range 1,ZeroCheckAt 23 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 6:=by decide +kernel
  exact zeroAtFast_sound 23 6 hfast

theorem zr23p7:∀ i ∈ List.range 1,ZeroCheckAt 23 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 7:=by decide +kernel
  exact zeroAtFast_sound 23 7 hfast

theorem zr23p8:∀ i ∈ List.range 1,ZeroCheckAt 23 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 8:=by decide +kernel
  exact zeroAtFast_sound 23 8 hfast

theorem zr23p9:∀ i ∈ List.range 1,ZeroCheckAt 23 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 9:=by decide +kernel
  exact zeroAtFast_sound 23 9 hfast

theorem zr23p10:∀ i ∈ List.range 1,ZeroCheckAt 23 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 10:=by decide +kernel
  exact zeroAtFast_sound 23 10 hfast

theorem zr23p11:∀ i ∈ List.range 1,ZeroCheckAt 23 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 11:=by decide +kernel
  exact zeroAtFast_sound 23 11 hfast

theorem zr23p12:∀ i ∈ List.range 1,ZeroCheckAt 23 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 12:=by decide +kernel
  exact zeroAtFast_sound 23 12 hfast

theorem zr23p13:∀ i ∈ List.range 1,ZeroCheckAt 23 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 13:=by decide +kernel
  exact zeroAtFast_sound 23 13 hfast

theorem zr23p14:∀ i ∈ List.range 1,ZeroCheckAt 23 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 14:=by decide +kernel
  exact zeroAtFast_sound 23 14 hfast

theorem zr23p15:∀ i ∈ List.range 1,ZeroCheckAt 23 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 23 15:=by decide +kernel
  exact zeroAtFast_sound 23 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
