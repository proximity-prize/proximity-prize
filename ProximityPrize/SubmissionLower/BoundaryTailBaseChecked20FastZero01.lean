import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zr20p0:∀ i ∈ List.range 1,ZeroCheckAt 20 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 0:=by decide +kernel
  exact zeroAtFast_sound 20 0 hfast

theorem zr20p1:∀ i ∈ List.range 1,ZeroCheckAt 20 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 1:=by decide +kernel
  exact zeroAtFast_sound 20 1 hfast

theorem zr20p2:∀ i ∈ List.range 1,ZeroCheckAt 20 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 2:=by decide +kernel
  exact zeroAtFast_sound 20 2 hfast

theorem zr20p3:∀ i ∈ List.range 1,ZeroCheckAt 20 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 3:=by decide +kernel
  exact zeroAtFast_sound 20 3 hfast

theorem zr20p4:∀ i ∈ List.range 1,ZeroCheckAt 20 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 4:=by decide +kernel
  exact zeroAtFast_sound 20 4 hfast

theorem zr20p5:∀ i ∈ List.range 1,ZeroCheckAt 20 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 5:=by decide +kernel
  exact zeroAtFast_sound 20 5 hfast

theorem zr20p6:∀ i ∈ List.range 1,ZeroCheckAt 20 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 6:=by decide +kernel
  exact zeroAtFast_sound 20 6 hfast

theorem zr20p7:∀ i ∈ List.range 1,ZeroCheckAt 20 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 7:=by decide +kernel
  exact zeroAtFast_sound 20 7 hfast

theorem zr20p8:∀ i ∈ List.range 1,ZeroCheckAt 20 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 8:=by decide +kernel
  exact zeroAtFast_sound 20 8 hfast

theorem zr20p9:∀ i ∈ List.range 1,ZeroCheckAt 20 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 9:=by decide +kernel
  exact zeroAtFast_sound 20 9 hfast

theorem zr20p10:∀ i ∈ List.range 1,ZeroCheckAt 20 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 10:=by decide +kernel
  exact zeroAtFast_sound 20 10 hfast

theorem zr20p11:∀ i ∈ List.range 1,ZeroCheckAt 20 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 11:=by decide +kernel
  exact zeroAtFast_sound 20 11 hfast

theorem zr20p12:∀ i ∈ List.range 1,ZeroCheckAt 20 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 12:=by decide +kernel
  exact zeroAtFast_sound 20 12 hfast

theorem zr20p13:∀ i ∈ List.range 1,ZeroCheckAt 20 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 13:=by decide +kernel
  exact zeroAtFast_sound 20 13 hfast

theorem zr20p14:∀ i ∈ List.range 1,ZeroCheckAt 20 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 14:=by decide +kernel
  exact zeroAtFast_sound 20 14 hfast

theorem zr20p15:∀ i ∈ List.range 1,ZeroCheckAt 20 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast:ZeroAtFast 20 15:=by decide +kernel
  exact zeroAtFast_sound 20 15 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
