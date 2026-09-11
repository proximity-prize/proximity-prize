import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr14p0:∀ i ∈ List.range 1,ZeroCheckAt 14 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 0:=by decide +kernel
  exact zeroAtFast_sound 14 0 hfast

theorem zr14p1:∀ i ∈ List.range 1,ZeroCheckAt 14 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 1:=by decide +kernel
  exact zeroAtFast_sound 14 1 hfast

theorem zr14p2:∀ i ∈ List.range 1,ZeroCheckAt 14 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 2:=by decide +kernel
  exact zeroAtFast_sound 14 2 hfast

theorem zr14p3:∀ i ∈ List.range 1,ZeroCheckAt 14 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 3:=by decide +kernel
  exact zeroAtFast_sound 14 3 hfast

theorem zr14p4:∀ i ∈ List.range 1,ZeroCheckAt 14 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 4:=by decide +kernel
  exact zeroAtFast_sound 14 4 hfast

theorem zr14p5:∀ i ∈ List.range 1,ZeroCheckAt 14 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 5:=by decide +kernel
  exact zeroAtFast_sound 14 5 hfast

theorem zr14p6:∀ i ∈ List.range 1,ZeroCheckAt 14 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 6:=by decide +kernel
  exact zeroAtFast_sound 14 6 hfast

theorem zr14p7:∀ i ∈ List.range 1,ZeroCheckAt 14 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 7:=by decide +kernel
  exact zeroAtFast_sound 14 7 hfast

theorem zr14p8:∀ i ∈ List.range 1,ZeroCheckAt 14 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 8:=by decide +kernel
  exact zeroAtFast_sound 14 8 hfast

theorem zr14p9:∀ i ∈ List.range 1,ZeroCheckAt 14 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 9:=by decide +kernel
  exact zeroAtFast_sound 14 9 hfast

theorem zr14p10:∀ i ∈ List.range 1,ZeroCheckAt 14 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 10:=by decide +kernel
  exact zeroAtFast_sound 14 10 hfast

theorem zr14p11:∀ i ∈ List.range 1,ZeroCheckAt 14 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 11:=by decide +kernel
  exact zeroAtFast_sound 14 11 hfast

theorem zr14p12:∀ i ∈ List.range 1,ZeroCheckAt 14 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 12:=by decide +kernel
  exact zeroAtFast_sound 14 12 hfast

theorem zr14p13:∀ i ∈ List.range 1,ZeroCheckAt 14 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 13:=by decide +kernel
  exact zeroAtFast_sound 14 13 hfast

theorem zr14p14:∀ i ∈ List.range 1,ZeroCheckAt 14 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 14:=by decide +kernel
  exact zeroAtFast_sound 14 14 hfast

theorem zr14p15:∀ i ∈ List.range 1,ZeroCheckAt 14 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 14 15:=by decide +kernel
  exact zeroAtFast_sound 14 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
