import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p0:∀ i ∈ List.range 1,StrictCheckAt 14 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 0) 14 0:=by decide +kernel
  exact strictAtFast_sound (row 14 0) 14 0 hvalid hfast

theorem sr14p1:∀ i ∈ List.range 1,StrictCheckAt 14 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 1) 14 1:=by decide +kernel
  exact strictAtFast_sound (row 14 1) 14 1 hvalid hfast

theorem sr14p2:∀ i ∈ List.range 1,StrictCheckAt 14 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 2) 14 2:=by decide +kernel
  exact strictAtFast_sound (row 14 2) 14 2 hvalid hfast

theorem sr14p3:∀ i ∈ List.range 1,StrictCheckAt 14 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 3) 14 3:=by decide +kernel
  exact strictAtFast_sound (row 14 3) 14 3 hvalid hfast

theorem sr14p4:∀ i ∈ List.range 1,StrictCheckAt 14 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 4) 14 4:=by decide +kernel
  exact strictAtFast_sound (row 14 4) 14 4 hvalid hfast

theorem sr14p5:∀ i ∈ List.range 1,StrictCheckAt 14 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 5) 14 5:=by decide +kernel
  exact strictAtFast_sound (row 14 5) 14 5 hvalid hfast

theorem sr14p6:∀ i ∈ List.range 1,StrictCheckAt 14 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 6) 14 6:=by decide +kernel
  exact strictAtFast_sound (row 14 6) 14 6 hvalid hfast

theorem sr14p7:∀ i ∈ List.range 1,StrictCheckAt 14 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 7) 14 7:=by decide +kernel
  exact strictAtFast_sound (row 14 7) 14 7 hvalid hfast

theorem sr14p8:∀ i ∈ List.range 1,StrictCheckAt 14 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 8) 14 8:=by decide +kernel
  exact strictAtFast_sound (row 14 8) 14 8 hvalid hfast

theorem sr14p9:∀ i ∈ List.range 1,StrictCheckAt 14 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 9) 14 9:=by decide +kernel
  exact strictAtFast_sound (row 14 9) 14 9 hvalid hfast

theorem sr14p10:∀ i ∈ List.range 1,StrictCheckAt 14 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 10) 14 10:=by decide +kernel
  exact strictAtFast_sound (row 14 10) 14 10 hvalid hfast

theorem sr14p11:∀ i ∈ List.range 1,StrictCheckAt 14 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 11) 14 11:=by decide +kernel
  exact strictAtFast_sound (row 14 11) 14 11 hvalid hfast

theorem sr14p12:∀ i ∈ List.range 1,StrictCheckAt 14 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 12) 14 12:=by decide +kernel
  exact strictAtFast_sound (row 14 12) 14 12 hvalid hfast

theorem sr14p13:∀ i ∈ List.range 1,StrictCheckAt 14 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 13) 14 13:=by decide +kernel
  exact strictAtFast_sound (row 14 13) 14 13 hvalid hfast

theorem sr14p14:∀ i ∈ List.range 1,StrictCheckAt 14 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 14) 14 14:=by decide +kernel
  exact strictAtFast_sound (row 14 14) 14 14 hvalid hfast

theorem sr14p15:∀ i ∈ List.range 1,StrictCheckAt 14 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 15) 14 15:=by decide +kernel
  exact strictAtFast_sound (row 14 15) 14 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
