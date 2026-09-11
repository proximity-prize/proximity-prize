import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr20p0:∀ i ∈ List.range 1,StrictCheckAt 20 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 0) 20 0:=by decide +kernel
  exact strictAtFast_sound (row 20 0) 20 0 hvalid hfast

theorem sr20p1:∀ i ∈ List.range 1,StrictCheckAt 20 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 1) 20 1:=by decide +kernel
  exact strictAtFast_sound (row 20 1) 20 1 hvalid hfast

theorem sr20p2:∀ i ∈ List.range 1,StrictCheckAt 20 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 2) 20 2:=by decide +kernel
  exact strictAtFast_sound (row 20 2) 20 2 hvalid hfast

theorem sr20p3:∀ i ∈ List.range 1,StrictCheckAt 20 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 3) 20 3:=by decide +kernel
  exact strictAtFast_sound (row 20 3) 20 3 hvalid hfast

theorem sr20p4:∀ i ∈ List.range 1,StrictCheckAt 20 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 4) 20 4:=by decide +kernel
  exact strictAtFast_sound (row 20 4) 20 4 hvalid hfast

theorem sr20p5:∀ i ∈ List.range 1,StrictCheckAt 20 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 5) 20 5:=by decide +kernel
  exact strictAtFast_sound (row 20 5) 20 5 hvalid hfast

theorem sr20p6:∀ i ∈ List.range 1,StrictCheckAt 20 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 6) 20 6:=by decide +kernel
  exact strictAtFast_sound (row 20 6) 20 6 hvalid hfast

theorem sr20p7:∀ i ∈ List.range 1,StrictCheckAt 20 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 7) 20 7:=by decide +kernel
  exact strictAtFast_sound (row 20 7) 20 7 hvalid hfast

theorem sr20p8:∀ i ∈ List.range 1,StrictCheckAt 20 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 8) 20 8:=by decide +kernel
  exact strictAtFast_sound (row 20 8) 20 8 hvalid hfast

theorem sr20p9:∀ i ∈ List.range 1,StrictCheckAt 20 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 9) 20 9:=by decide +kernel
  exact strictAtFast_sound (row 20 9) 20 9 hvalid hfast

theorem sr20p10:∀ i ∈ List.range 1,StrictCheckAt 20 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 10) 20 10:=by decide +kernel
  exact strictAtFast_sound (row 20 10) 20 10 hvalid hfast

theorem sr20p11:∀ i ∈ List.range 1,StrictCheckAt 20 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 11) 20 11:=by decide +kernel
  exact strictAtFast_sound (row 20 11) 20 11 hvalid hfast

theorem sr20p12:∀ i ∈ List.range 1,StrictCheckAt 20 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 12) 20 12:=by decide +kernel
  exact strictAtFast_sound (row 20 12) 20 12 hvalid hfast

theorem sr20p13:∀ i ∈ List.range 1,StrictCheckAt 20 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 13) 20 13:=by decide +kernel
  exact strictAtFast_sound (row 20 13) 20 13 hvalid hfast

theorem sr20p14:∀ i ∈ List.range 1,StrictCheckAt 20 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 14) 20 14:=by decide +kernel
  exact strictAtFast_sound (row 20 14) 20 14 hvalid hfast

theorem sr20p15:∀ i ∈ List.range 1,StrictCheckAt 20 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 20 15) 20 15:=by decide +kernel
  exact strictAtFast_sound (row 20 15) 20 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
