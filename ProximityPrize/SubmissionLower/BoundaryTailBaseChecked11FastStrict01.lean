import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr11p0:∀ i ∈ List.range 1,StrictCheckAt 11 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 0) 11 0:=by decide +kernel
  exact strictAtFast_sound (row 11 0) 11 0 hvalid hfast

theorem sr11p1:∀ i ∈ List.range 1,StrictCheckAt 11 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 1) 11 1:=by decide +kernel
  exact strictAtFast_sound (row 11 1) 11 1 hvalid hfast

theorem sr11p2:∀ i ∈ List.range 1,StrictCheckAt 11 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 2) 11 2:=by decide +kernel
  exact strictAtFast_sound (row 11 2) 11 2 hvalid hfast

theorem sr11p3:∀ i ∈ List.range 1,StrictCheckAt 11 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 3) 11 3:=by decide +kernel
  exact strictAtFast_sound (row 11 3) 11 3 hvalid hfast

theorem sr11p4:∀ i ∈ List.range 1,StrictCheckAt 11 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 4) 11 4:=by decide +kernel
  exact strictAtFast_sound (row 11 4) 11 4 hvalid hfast

theorem sr11p5:∀ i ∈ List.range 1,StrictCheckAt 11 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 5) 11 5:=by decide +kernel
  exact strictAtFast_sound (row 11 5) 11 5 hvalid hfast

theorem sr11p6:∀ i ∈ List.range 1,StrictCheckAt 11 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 6) 11 6:=by decide +kernel
  exact strictAtFast_sound (row 11 6) 11 6 hvalid hfast

theorem sr11p7:∀ i ∈ List.range 1,StrictCheckAt 11 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 7) 11 7:=by decide +kernel
  exact strictAtFast_sound (row 11 7) 11 7 hvalid hfast

theorem sr11p8:∀ i ∈ List.range 1,StrictCheckAt 11 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 8) 11 8:=by decide +kernel
  exact strictAtFast_sound (row 11 8) 11 8 hvalid hfast

theorem sr11p9:∀ i ∈ List.range 1,StrictCheckAt 11 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 9) 11 9:=by decide +kernel
  exact strictAtFast_sound (row 11 9) 11 9 hvalid hfast

theorem sr11p10:∀ i ∈ List.range 1,StrictCheckAt 11 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 10) 11 10:=by decide +kernel
  exact strictAtFast_sound (row 11 10) 11 10 hvalid hfast

theorem sr11p11:∀ i ∈ List.range 1,StrictCheckAt 11 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 11) 11 11:=by decide +kernel
  exact strictAtFast_sound (row 11 11) 11 11 hvalid hfast

theorem sr11p12:∀ i ∈ List.range 1,StrictCheckAt 11 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 12) 11 12:=by decide +kernel
  exact strictAtFast_sound (row 11 12) 11 12 hvalid hfast

theorem sr11p13:∀ i ∈ List.range 1,StrictCheckAt 11 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 13) 11 13:=by decide +kernel
  exact strictAtFast_sound (row 11 13) 11 13 hvalid hfast

theorem sr11p14:∀ i ∈ List.range 1,StrictCheckAt 11 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 14) 11 14:=by decide +kernel
  exact strictAtFast_sound (row 11 14) 11 14 hvalid hfast

theorem sr11p15:∀ i ∈ List.range 1,StrictCheckAt 11 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 11 15) 11 15:=by decide +kernel
  exact strictAtFast_sound (row 11 15) 11 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
