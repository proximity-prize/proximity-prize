import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr28p0:∀ i ∈ List.range 1,StrictCheckAt 28 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 0) 28 0:=by decide +kernel
  exact strictAtFast_sound (row 28 0) 28 0 hvalid hfast

theorem sr28p1:∀ i ∈ List.range 1,StrictCheckAt 28 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 1) 28 1:=by decide +kernel
  exact strictAtFast_sound (row 28 1) 28 1 hvalid hfast

theorem sr28p2:∀ i ∈ List.range 1,StrictCheckAt 28 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 2) 28 2:=by decide +kernel
  exact strictAtFast_sound (row 28 2) 28 2 hvalid hfast

theorem sr28p3:∀ i ∈ List.range 1,StrictCheckAt 28 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 3) 28 3:=by decide +kernel
  exact strictAtFast_sound (row 28 3) 28 3 hvalid hfast

theorem sr28p4:∀ i ∈ List.range 1,StrictCheckAt 28 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 4) 28 4:=by decide +kernel
  exact strictAtFast_sound (row 28 4) 28 4 hvalid hfast

theorem sr28p5:∀ i ∈ List.range 1,StrictCheckAt 28 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 5) 28 5:=by decide +kernel
  exact strictAtFast_sound (row 28 5) 28 5 hvalid hfast

theorem sr28p6:∀ i ∈ List.range 1,StrictCheckAt 28 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 6) 28 6:=by decide +kernel
  exact strictAtFast_sound (row 28 6) 28 6 hvalid hfast

theorem sr28p7:∀ i ∈ List.range 1,StrictCheckAt 28 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 7) 28 7:=by decide +kernel
  exact strictAtFast_sound (row 28 7) 28 7 hvalid hfast

theorem sr28p8:∀ i ∈ List.range 1,StrictCheckAt 28 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 8) 28 8:=by decide +kernel
  exact strictAtFast_sound (row 28 8) 28 8 hvalid hfast

theorem sr28p9:∀ i ∈ List.range 1,StrictCheckAt 28 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 9) 28 9:=by decide +kernel
  exact strictAtFast_sound (row 28 9) 28 9 hvalid hfast

theorem sr28p10:∀ i ∈ List.range 1,StrictCheckAt 28 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 10) 28 10:=by decide +kernel
  exact strictAtFast_sound (row 28 10) 28 10 hvalid hfast

theorem sr28p11:∀ i ∈ List.range 1,StrictCheckAt 28 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 11) 28 11:=by decide +kernel
  exact strictAtFast_sound (row 28 11) 28 11 hvalid hfast

theorem sr28p12:∀ i ∈ List.range 1,StrictCheckAt 28 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 12) 28 12:=by decide +kernel
  exact strictAtFast_sound (row 28 12) 28 12 hvalid hfast

theorem sr28p13:∀ i ∈ List.range 1,StrictCheckAt 28 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 13) 28 13:=by decide +kernel
  exact strictAtFast_sound (row 28 13) 28 13 hvalid hfast

theorem sr28p14:∀ i ∈ List.range 1,StrictCheckAt 28 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 14) 28 14:=by decide +kernel
  exact strictAtFast_sound (row 28 14) 28 14 hvalid hfast

theorem sr28p15:∀ i ∈ List.range 1,StrictCheckAt 28 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 15) 28 15:=by decide +kernel
  exact strictAtFast_sound (row 28 15) 28 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
