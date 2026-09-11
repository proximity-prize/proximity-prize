import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr31p0:∀ i ∈ List.range 1,ZeroCheckAt 31 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 0:=by decide +kernel
  exact zeroAtFast_sound 31 0 hfast

theorem zr31p1:∀ i ∈ List.range 1,ZeroCheckAt 31 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 1:=by decide +kernel
  exact zeroAtFast_sound 31 1 hfast

theorem zr31p2:∀ i ∈ List.range 1,ZeroCheckAt 31 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 2:=by decide +kernel
  exact zeroAtFast_sound 31 2 hfast

theorem zr31p3:∀ i ∈ List.range 1,ZeroCheckAt 31 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 3:=by decide +kernel
  exact zeroAtFast_sound 31 3 hfast

theorem zr31p4:∀ i ∈ List.range 1,ZeroCheckAt 31 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 4:=by decide +kernel
  exact zeroAtFast_sound 31 4 hfast

theorem zr31p5:∀ i ∈ List.range 1,ZeroCheckAt 31 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 5:=by decide +kernel
  exact zeroAtFast_sound 31 5 hfast

theorem zr31p6:∀ i ∈ List.range 1,ZeroCheckAt 31 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 6:=by decide +kernel
  exact zeroAtFast_sound 31 6 hfast

theorem zr31p7:∀ i ∈ List.range 1,ZeroCheckAt 31 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 7:=by decide +kernel
  exact zeroAtFast_sound 31 7 hfast

theorem zr31p8:∀ i ∈ List.range 1,ZeroCheckAt 31 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 8:=by decide +kernel
  exact zeroAtFast_sound 31 8 hfast

theorem zr31p9:∀ i ∈ List.range 1,ZeroCheckAt 31 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 9:=by decide +kernel
  exact zeroAtFast_sound 31 9 hfast

theorem zr31p10:∀ i ∈ List.range 1,ZeroCheckAt 31 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 10:=by decide +kernel
  exact zeroAtFast_sound 31 10 hfast

theorem zr31p11:∀ i ∈ List.range 1,ZeroCheckAt 31 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 11:=by decide +kernel
  exact zeroAtFast_sound 31 11 hfast

theorem zr31p12:∀ i ∈ List.range 1,ZeroCheckAt 31 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 12:=by decide +kernel
  exact zeroAtFast_sound 31 12 hfast

theorem zr31p13:∀ i ∈ List.range 1,ZeroCheckAt 31 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 13:=by decide +kernel
  exact zeroAtFast_sound 31 13 hfast

theorem zr31p14:∀ i ∈ List.range 1,ZeroCheckAt 31 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 14:=by decide +kernel
  exact zeroAtFast_sound 31 14 hfast

theorem zr31p15:∀ i ∈ List.range 1,ZeroCheckAt 31 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 31 15:=by decide +kernel
  exact zeroAtFast_sound 31 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
