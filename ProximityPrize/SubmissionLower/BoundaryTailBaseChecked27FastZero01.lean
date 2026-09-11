import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr27p0:∀ i ∈ List.range 1,ZeroCheckAt 27 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 0:=by decide +kernel
  exact zeroAtFast_sound 27 0 hfast

theorem zr27p1:∀ i ∈ List.range 1,ZeroCheckAt 27 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 1:=by decide +kernel
  exact zeroAtFast_sound 27 1 hfast

theorem zr27p2:∀ i ∈ List.range 1,ZeroCheckAt 27 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 2:=by decide +kernel
  exact zeroAtFast_sound 27 2 hfast

theorem zr27p3:∀ i ∈ List.range 1,ZeroCheckAt 27 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 3:=by decide +kernel
  exact zeroAtFast_sound 27 3 hfast

theorem zr27p4:∀ i ∈ List.range 1,ZeroCheckAt 27 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 4:=by decide +kernel
  exact zeroAtFast_sound 27 4 hfast

theorem zr27p5:∀ i ∈ List.range 1,ZeroCheckAt 27 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 5:=by decide +kernel
  exact zeroAtFast_sound 27 5 hfast

theorem zr27p6:∀ i ∈ List.range 1,ZeroCheckAt 27 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 6:=by decide +kernel
  exact zeroAtFast_sound 27 6 hfast

theorem zr27p7:∀ i ∈ List.range 1,ZeroCheckAt 27 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 7:=by decide +kernel
  exact zeroAtFast_sound 27 7 hfast

theorem zr27p8:∀ i ∈ List.range 1,ZeroCheckAt 27 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 8:=by decide +kernel
  exact zeroAtFast_sound 27 8 hfast

theorem zr27p9:∀ i ∈ List.range 1,ZeroCheckAt 27 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 9:=by decide +kernel
  exact zeroAtFast_sound 27 9 hfast

theorem zr27p10:∀ i ∈ List.range 1,ZeroCheckAt 27 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 10:=by decide +kernel
  exact zeroAtFast_sound 27 10 hfast

theorem zr27p11:∀ i ∈ List.range 1,ZeroCheckAt 27 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 11:=by decide +kernel
  exact zeroAtFast_sound 27 11 hfast

theorem zr27p12:∀ i ∈ List.range 1,ZeroCheckAt 27 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 12:=by decide +kernel
  exact zeroAtFast_sound 27 12 hfast

theorem zr27p13:∀ i ∈ List.range 1,ZeroCheckAt 27 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 13:=by decide +kernel
  exact zeroAtFast_sound 27 13 hfast

theorem zr27p14:∀ i ∈ List.range 1,ZeroCheckAt 27 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 14:=by decide +kernel
  exact zeroAtFast_sound 27 14 hfast

theorem zr27p15:∀ i ∈ List.range 1,ZeroCheckAt 27 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 27 15:=by decide +kernel
  exact zeroAtFast_sound 27 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
