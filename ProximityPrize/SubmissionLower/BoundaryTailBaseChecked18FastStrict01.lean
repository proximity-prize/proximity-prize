import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr18p0:∀ i ∈ List.range 1,StrictCheckAt 18 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 0) 18 0:=by decide +kernel
  exact strictAtFast_sound (row 18 0) 18 0 hvalid hfast

theorem sr18p1:∀ i ∈ List.range 1,StrictCheckAt 18 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 1) 18 1:=by decide +kernel
  exact strictAtFast_sound (row 18 1) 18 1 hvalid hfast

theorem sr18p2:∀ i ∈ List.range 1,StrictCheckAt 18 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 2) 18 2:=by decide +kernel
  exact strictAtFast_sound (row 18 2) 18 2 hvalid hfast

theorem sr18p3:∀ i ∈ List.range 1,StrictCheckAt 18 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 3) 18 3:=by decide +kernel
  exact strictAtFast_sound (row 18 3) 18 3 hvalid hfast

theorem sr18p4:∀ i ∈ List.range 1,StrictCheckAt 18 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 4) 18 4:=by decide +kernel
  exact strictAtFast_sound (row 18 4) 18 4 hvalid hfast

theorem sr18p5:∀ i ∈ List.range 1,StrictCheckAt 18 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 5) 18 5:=by decide +kernel
  exact strictAtFast_sound (row 18 5) 18 5 hvalid hfast

theorem sr18p6:∀ i ∈ List.range 1,StrictCheckAt 18 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 6) 18 6:=by decide +kernel
  exact strictAtFast_sound (row 18 6) 18 6 hvalid hfast

theorem sr18p7:∀ i ∈ List.range 1,StrictCheckAt 18 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 7) 18 7:=by decide +kernel
  exact strictAtFast_sound (row 18 7) 18 7 hvalid hfast

theorem sr18p8:∀ i ∈ List.range 1,StrictCheckAt 18 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 8) 18 8:=by decide +kernel
  exact strictAtFast_sound (row 18 8) 18 8 hvalid hfast

theorem sr18p9:∀ i ∈ List.range 1,StrictCheckAt 18 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 9) 18 9:=by decide +kernel
  exact strictAtFast_sound (row 18 9) 18 9 hvalid hfast

theorem sr18p10:∀ i ∈ List.range 1,StrictCheckAt 18 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 10) 18 10:=by decide +kernel
  exact strictAtFast_sound (row 18 10) 18 10 hvalid hfast

theorem sr18p11:∀ i ∈ List.range 1,StrictCheckAt 18 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 11) 18 11:=by decide +kernel
  exact strictAtFast_sound (row 18 11) 18 11 hvalid hfast

theorem sr18p12:∀ i ∈ List.range 1,StrictCheckAt 18 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 12) 18 12:=by decide +kernel
  exact strictAtFast_sound (row 18 12) 18 12 hvalid hfast

theorem sr18p13:∀ i ∈ List.range 1,StrictCheckAt 18 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 13) 18 13:=by decide +kernel
  exact strictAtFast_sound (row 18 13) 18 13 hvalid hfast

theorem sr18p14:∀ i ∈ List.range 1,StrictCheckAt 18 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 14) 18 14:=by decide +kernel
  exact strictAtFast_sound (row 18 14) 18 14 hvalid hfast

theorem sr18p15:∀ i ∈ List.range 1,StrictCheckAt 18 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 18 15) 18 15:=by decide +kernel
  exact strictAtFast_sound (row 18 15) 18 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
