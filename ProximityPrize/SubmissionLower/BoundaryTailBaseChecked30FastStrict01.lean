import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr30p0:∀ i ∈ List.range 1,StrictCheckAt 30 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 0) 30 0:=by decide +kernel
  exact strictAtFast_sound (row 30 0) 30 0 hvalid hfast

theorem sr30p1:∀ i ∈ List.range 1,StrictCheckAt 30 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 1) 30 1:=by decide +kernel
  exact strictAtFast_sound (row 30 1) 30 1 hvalid hfast

theorem sr30p2:∀ i ∈ List.range 1,StrictCheckAt 30 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 2) 30 2:=by decide +kernel
  exact strictAtFast_sound (row 30 2) 30 2 hvalid hfast

theorem sr30p3:∀ i ∈ List.range 1,StrictCheckAt 30 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 3) 30 3:=by decide +kernel
  exact strictAtFast_sound (row 30 3) 30 3 hvalid hfast

theorem sr30p4:∀ i ∈ List.range 1,StrictCheckAt 30 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 4) 30 4:=by decide +kernel
  exact strictAtFast_sound (row 30 4) 30 4 hvalid hfast

theorem sr30p5:∀ i ∈ List.range 1,StrictCheckAt 30 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 5) 30 5:=by decide +kernel
  exact strictAtFast_sound (row 30 5) 30 5 hvalid hfast

theorem sr30p6:∀ i ∈ List.range 1,StrictCheckAt 30 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 6) 30 6:=by decide +kernel
  exact strictAtFast_sound (row 30 6) 30 6 hvalid hfast

theorem sr30p7:∀ i ∈ List.range 1,StrictCheckAt 30 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 7) 30 7:=by decide +kernel
  exact strictAtFast_sound (row 30 7) 30 7 hvalid hfast

theorem sr30p8:∀ i ∈ List.range 1,StrictCheckAt 30 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 8) 30 8:=by decide +kernel
  exact strictAtFast_sound (row 30 8) 30 8 hvalid hfast

theorem sr30p9:∀ i ∈ List.range 1,StrictCheckAt 30 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 9) 30 9:=by decide +kernel
  exact strictAtFast_sound (row 30 9) 30 9 hvalid hfast

theorem sr30p10:∀ i ∈ List.range 1,StrictCheckAt 30 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 10) 30 10:=by decide +kernel
  exact strictAtFast_sound (row 30 10) 30 10 hvalid hfast

theorem sr30p11:∀ i ∈ List.range 1,StrictCheckAt 30 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 11) 30 11:=by decide +kernel
  exact strictAtFast_sound (row 30 11) 30 11 hvalid hfast

theorem sr30p12:∀ i ∈ List.range 1,StrictCheckAt 30 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 12) 30 12:=by decide +kernel
  exact strictAtFast_sound (row 30 12) 30 12 hvalid hfast

theorem sr30p13:∀ i ∈ List.range 1,StrictCheckAt 30 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 13) 30 13:=by decide +kernel
  exact strictAtFast_sound (row 30 13) 30 13 hvalid hfast

theorem sr30p14:∀ i ∈ List.range 1,StrictCheckAt 30 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 14) 30 14:=by decide +kernel
  exact strictAtFast_sound (row 30 14) 30 14 hvalid hfast

theorem sr30p15:∀ i ∈ List.range 1,StrictCheckAt 30 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 30 15) 30 15:=by decide +kernel
  exact strictAtFast_sound (row 30 15) 30 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
