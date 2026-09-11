import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastZero09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr9p0:∀ i ∈ List.range 1,StrictCheckAt 9 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 0 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 0) 9 0:=by decide +kernel
  exact strictAtFast_sound (row 9 0) 9 0 hvalid hfast

theorem sr9p1:∀ i ∈ List.range 1,StrictCheckAt 9 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 1 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 1) 9 1:=by decide +kernel
  exact strictAtFast_sound (row 9 1) 9 1 hvalid hfast

theorem sr9p2:∀ i ∈ List.range 1,StrictCheckAt 9 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 2 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 2) 9 2:=by decide +kernel
  exact strictAtFast_sound (row 9 2) 9 2 hvalid hfast

theorem sr9p3:∀ i ∈ List.range 1,StrictCheckAt 9 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 3 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 3) 9 3:=by decide +kernel
  exact strictAtFast_sound (row 9 3) 9 3 hvalid hfast

theorem sr9p4:∀ i ∈ List.range 1,StrictCheckAt 9 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 4 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 4) 9 4:=by decide +kernel
  exact strictAtFast_sound (row 9 4) 9 4 hvalid hfast

theorem sr9p5:∀ i ∈ List.range 1,StrictCheckAt 9 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 5 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 5) 9 5:=by decide +kernel
  exact strictAtFast_sound (row 9 5) 9 5 hvalid hfast

theorem sr9p6:∀ i ∈ List.range 1,StrictCheckAt 9 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 6 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 6) 9 6:=by decide +kernel
  exact strictAtFast_sound (row 9 6) 9 6 hvalid hfast

theorem sr9p7:∀ i ∈ List.range 1,StrictCheckAt 9 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 7 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 7) 9 7:=by decide +kernel
  exact strictAtFast_sound (row 9 7) 9 7 hvalid hfast

theorem sr9p8:∀ i ∈ List.range 1,StrictCheckAt 9 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 8 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 8) 9 8:=by decide +kernel
  exact strictAtFast_sound (row 9 8) 9 8 hvalid hfast

theorem sr9p9:∀ i ∈ List.range 1,StrictCheckAt 9 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 9 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 9) 9 9:=by decide +kernel
  exact strictAtFast_sound (row 9 9) 9 9 hvalid hfast

theorem sr9p10:∀ i ∈ List.range 1,StrictCheckAt 9 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 10 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 10) 9 10:=by decide +kernel
  exact strictAtFast_sound (row 9 10) 9 10 hvalid hfast

theorem sr9p11:∀ i ∈ List.range 1,StrictCheckAt 9 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 11 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 11) 9 11:=by decide +kernel
  exact strictAtFast_sound (row 9 11) 9 11 hvalid hfast

theorem sr9p12:∀ i ∈ List.range 1,StrictCheckAt 9 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 12 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 12) 9 12:=by decide +kernel
  exact strictAtFast_sound (row 9 12) 9 12 hvalid hfast

theorem sr9p13:∀ i ∈ List.range 1,StrictCheckAt 9 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 13 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 13) 9 13:=by decide +kernel
  exact strictAtFast_sound (row 9 13) 9 13 hvalid hfast

theorem sr9p14:∀ i ∈ List.range 1,StrictCheckAt 9 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 14 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 14) 9 14:=by decide +kernel
  exact strictAtFast_sound (row 9 14) 9 14 hvalid hfast

theorem sr9p15:∀ i ∈ List.range 1,StrictCheckAt 9 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 15 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 9 15) 9 15:=by decide +kernel
  exact strictAtFast_sound (row 9 15) 9 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
