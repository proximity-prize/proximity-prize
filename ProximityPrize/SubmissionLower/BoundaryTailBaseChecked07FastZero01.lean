import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr7p0:∀ i ∈ List.range 1,ZeroCheckAt 7 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 0:=by decide +kernel
  exact zeroAtFast_sound 7 0 hfast

theorem zr7p1:∀ i ∈ List.range 1,ZeroCheckAt 7 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 1:=by decide +kernel
  exact zeroAtFast_sound 7 1 hfast

theorem zr7p2:∀ i ∈ List.range 1,ZeroCheckAt 7 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 2:=by decide +kernel
  exact zeroAtFast_sound 7 2 hfast

theorem zr7p3:∀ i ∈ List.range 1,ZeroCheckAt 7 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 3:=by decide +kernel
  exact zeroAtFast_sound 7 3 hfast

theorem zr7p4:∀ i ∈ List.range 1,ZeroCheckAt 7 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 4:=by decide +kernel
  exact zeroAtFast_sound 7 4 hfast

theorem zr7p5:∀ i ∈ List.range 1,ZeroCheckAt 7 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 5:=by decide +kernel
  exact zeroAtFast_sound 7 5 hfast

theorem zr7p6:∀ i ∈ List.range 1,ZeroCheckAt 7 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 6:=by decide +kernel
  exact zeroAtFast_sound 7 6 hfast

theorem zr7p7:∀ i ∈ List.range 1,ZeroCheckAt 7 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 7:=by decide +kernel
  exact zeroAtFast_sound 7 7 hfast

theorem zr7p8:∀ i ∈ List.range 1,ZeroCheckAt 7 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 8:=by decide +kernel
  exact zeroAtFast_sound 7 8 hfast

theorem zr7p9:∀ i ∈ List.range 1,ZeroCheckAt 7 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 9:=by decide +kernel
  exact zeroAtFast_sound 7 9 hfast

theorem zr7p10:∀ i ∈ List.range 1,ZeroCheckAt 7 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 10:=by decide +kernel
  exact zeroAtFast_sound 7 10 hfast

theorem zr7p11:∀ i ∈ List.range 1,ZeroCheckAt 7 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 11:=by decide +kernel
  exact zeroAtFast_sound 7 11 hfast

theorem zr7p12:∀ i ∈ List.range 1,ZeroCheckAt 7 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 12:=by decide +kernel
  exact zeroAtFast_sound 7 12 hfast

theorem zr7p13:∀ i ∈ List.range 1,ZeroCheckAt 7 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 13:=by decide +kernel
  exact zeroAtFast_sound 7 13 hfast

theorem zr7p14:∀ i ∈ List.range 1,ZeroCheckAt 7 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 14:=by decide +kernel
  exact zeroAtFast_sound 7 14 hfast

theorem zr7p15:∀ i ∈ List.range 1,ZeroCheckAt 7 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 7 15:=by decide +kernel
  exact zeroAtFast_sound 7 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
