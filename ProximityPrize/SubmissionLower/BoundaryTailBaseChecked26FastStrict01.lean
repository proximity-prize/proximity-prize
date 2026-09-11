import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr26p0:∀ i ∈ List.range 1,StrictCheckAt 26 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 0) 26 0:=by decide +kernel
  exact strictAtFast_sound (row 26 0) 26 0 hvalid hfast

theorem sr26p1:∀ i ∈ List.range 1,StrictCheckAt 26 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 1) 26 1:=by decide +kernel
  exact strictAtFast_sound (row 26 1) 26 1 hvalid hfast

theorem sr26p2:∀ i ∈ List.range 1,StrictCheckAt 26 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 2) 26 2:=by decide +kernel
  exact strictAtFast_sound (row 26 2) 26 2 hvalid hfast

theorem sr26p3:∀ i ∈ List.range 1,StrictCheckAt 26 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 3) 26 3:=by decide +kernel
  exact strictAtFast_sound (row 26 3) 26 3 hvalid hfast

theorem sr26p4:∀ i ∈ List.range 1,StrictCheckAt 26 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 4) 26 4:=by decide +kernel
  exact strictAtFast_sound (row 26 4) 26 4 hvalid hfast

theorem sr26p5:∀ i ∈ List.range 1,StrictCheckAt 26 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 5) 26 5:=by decide +kernel
  exact strictAtFast_sound (row 26 5) 26 5 hvalid hfast

theorem sr26p6:∀ i ∈ List.range 1,StrictCheckAt 26 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 6) 26 6:=by decide +kernel
  exact strictAtFast_sound (row 26 6) 26 6 hvalid hfast

theorem sr26p7:∀ i ∈ List.range 1,StrictCheckAt 26 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 7) 26 7:=by decide +kernel
  exact strictAtFast_sound (row 26 7) 26 7 hvalid hfast

theorem sr26p8:∀ i ∈ List.range 1,StrictCheckAt 26 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 8) 26 8:=by decide +kernel
  exact strictAtFast_sound (row 26 8) 26 8 hvalid hfast

theorem sr26p9:∀ i ∈ List.range 1,StrictCheckAt 26 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 9) 26 9:=by decide +kernel
  exact strictAtFast_sound (row 26 9) 26 9 hvalid hfast

theorem sr26p10:∀ i ∈ List.range 1,StrictCheckAt 26 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 10) 26 10:=by decide +kernel
  exact strictAtFast_sound (row 26 10) 26 10 hvalid hfast

theorem sr26p11:∀ i ∈ List.range 1,StrictCheckAt 26 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 11) 26 11:=by decide +kernel
  exact strictAtFast_sound (row 26 11) 26 11 hvalid hfast

theorem sr26p12:∀ i ∈ List.range 1,StrictCheckAt 26 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 12) 26 12:=by decide +kernel
  exact strictAtFast_sound (row 26 12) 26 12 hvalid hfast

theorem sr26p13:∀ i ∈ List.range 1,StrictCheckAt 26 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 13) 26 13:=by decide +kernel
  exact strictAtFast_sound (row 26 13) 26 13 hvalid hfast

theorem sr26p14:∀ i ∈ List.range 1,StrictCheckAt 26 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 14) 26 14:=by decide +kernel
  exact strictAtFast_sound (row 26 14) 26 14 hvalid hfast

theorem sr26p15:∀ i ∈ List.range 1,StrictCheckAt 26 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 26 15) 26 15:=by decide +kernel
  exact strictAtFast_sound (row 26 15) 26 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
