import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr30p0:∀ i ∈ List.range 1,ZeroCheckAt 30 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 0:=by decide +kernel
  exact zeroAtFast_sound 30 0 hfast

theorem zr30p1:∀ i ∈ List.range 1,ZeroCheckAt 30 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 1:=by decide +kernel
  exact zeroAtFast_sound 30 1 hfast

theorem zr30p2:∀ i ∈ List.range 1,ZeroCheckAt 30 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 2:=by decide +kernel
  exact zeroAtFast_sound 30 2 hfast

theorem zr30p3:∀ i ∈ List.range 1,ZeroCheckAt 30 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 3:=by decide +kernel
  exact zeroAtFast_sound 30 3 hfast

theorem zr30p4:∀ i ∈ List.range 1,ZeroCheckAt 30 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 4:=by decide +kernel
  exact zeroAtFast_sound 30 4 hfast

theorem zr30p5:∀ i ∈ List.range 1,ZeroCheckAt 30 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 5:=by decide +kernel
  exact zeroAtFast_sound 30 5 hfast

theorem zr30p6:∀ i ∈ List.range 1,ZeroCheckAt 30 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 6:=by decide +kernel
  exact zeroAtFast_sound 30 6 hfast

theorem zr30p7:∀ i ∈ List.range 1,ZeroCheckAt 30 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 7:=by decide +kernel
  exact zeroAtFast_sound 30 7 hfast

theorem zr30p8:∀ i ∈ List.range 1,ZeroCheckAt 30 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 8:=by decide +kernel
  exact zeroAtFast_sound 30 8 hfast

theorem zr30p9:∀ i ∈ List.range 1,ZeroCheckAt 30 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 9:=by decide +kernel
  exact zeroAtFast_sound 30 9 hfast

theorem zr30p10:∀ i ∈ List.range 1,ZeroCheckAt 30 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 10:=by decide +kernel
  exact zeroAtFast_sound 30 10 hfast

theorem zr30p11:∀ i ∈ List.range 1,ZeroCheckAt 30 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 11:=by decide +kernel
  exact zeroAtFast_sound 30 11 hfast

theorem zr30p12:∀ i ∈ List.range 1,ZeroCheckAt 30 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 12:=by decide +kernel
  exact zeroAtFast_sound 30 12 hfast

theorem zr30p13:∀ i ∈ List.range 1,ZeroCheckAt 30 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 13:=by decide +kernel
  exact zeroAtFast_sound 30 13 hfast

theorem zr30p14:∀ i ∈ List.range 1,ZeroCheckAt 30 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 14:=by decide +kernel
  exact zeroAtFast_sound 30 14 hfast

theorem zr30p15:∀ i ∈ List.range 1,ZeroCheckAt 30 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 30 15:=by decide +kernel
  exact zeroAtFast_sound 30 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
