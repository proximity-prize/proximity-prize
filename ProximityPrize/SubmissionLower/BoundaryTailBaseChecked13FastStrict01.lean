import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr13p0:∀ i ∈ List.range 1,StrictCheckAt 13 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 0) 13 0:=by decide +kernel
  have hfast:StrictAtFast (row 13 0) 13 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 0) 13 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 0) 13 0 hvalid hfast

theorem sr13p1:∀ i ∈ List.range 1,StrictCheckAt 13 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 1) 13 1:=by decide +kernel
  have hfast:StrictAtFast (row 13 1) 13 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 1) 13 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 1) 13 1 hvalid hfast

theorem sr13p2:∀ i ∈ List.range 1,StrictCheckAt 13 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 2) 13 2:=by decide +kernel
  have hfast:StrictAtFast (row 13 2) 13 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 2) 13 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 2) 13 2 hvalid hfast

theorem sr13p3:∀ i ∈ List.range 1,StrictCheckAt 13 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 3) 13 3:=by decide +kernel
  have hfast:StrictAtFast (row 13 3) 13 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 3) 13 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 3) 13 3 hvalid hfast

theorem sr13p4:∀ i ∈ List.range 1,StrictCheckAt 13 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 4) 13 4:=by decide +kernel
  have hfast:StrictAtFast (row 13 4) 13 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 4) 13 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 4) 13 4 hvalid hfast

theorem sr13p5:∀ i ∈ List.range 1,StrictCheckAt 13 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 5) 13 5:=by decide +kernel
  have hfast:StrictAtFast (row 13 5) 13 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 5) 13 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 5) 13 5 hvalid hfast

theorem sr13p6:∀ i ∈ List.range 1,StrictCheckAt 13 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 6) 13 6:=by decide +kernel
  have hfast:StrictAtFast (row 13 6) 13 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 6) 13 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 6) 13 6 hvalid hfast

theorem sr13p7:∀ i ∈ List.range 1,StrictCheckAt 13 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 7) 13 7:=by decide +kernel
  have hfast:StrictAtFast (row 13 7) 13 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 7) 13 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 7) 13 7 hvalid hfast

theorem sr13p8:∀ i ∈ List.range 1,StrictCheckAt 13 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 8) 13 8:=by decide +kernel
  have hfast:StrictAtFast (row 13 8) 13 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 8) 13 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 8) 13 8 hvalid hfast

theorem sr13p9:∀ i ∈ List.range 1,StrictCheckAt 13 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 9) 13 9:=by decide +kernel
  have hfast:StrictAtFast (row 13 9) 13 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 9) 13 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 9) 13 9 hvalid hfast

theorem sr13p10:∀ i ∈ List.range 1,StrictCheckAt 13 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 10) 13 10:=by decide +kernel
  have hfast:StrictAtFast (row 13 10) 13 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 10) 13 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 10) 13 10 hvalid hfast

theorem sr13p11:∀ i ∈ List.range 1,StrictCheckAt 13 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 11) 13 11:=by decide +kernel
  have hfast:StrictAtFast (row 13 11) 13 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 11) 13 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 11) 13 11 hvalid hfast

theorem sr13p12:∀ i ∈ List.range 1,StrictCheckAt 13 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 12) 13 12:=by decide +kernel
  have hfast:StrictAtFast (row 13 12) 13 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 12) 13 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 12) 13 12 hvalid hfast

theorem sr13p13:∀ i ∈ List.range 1,StrictCheckAt 13 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 13) 13 13:=by decide +kernel
  have hfast:StrictAtFast (row 13 13) 13 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 13) 13 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 13) 13 13 hvalid hfast

theorem sr13p14:∀ i ∈ List.range 1,StrictCheckAt 13 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 14) 13 14:=by decide +kernel
  have hfast:StrictAtFast (row 13 14) 13 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 14) 13 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 14) 13 14 hvalid hfast

theorem sr13p15:∀ i ∈ List.range 1,StrictCheckAt 13 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 15) 13 15:=by decide +kernel
  have hfast:StrictAtFast (row 13 15) 13 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 15) 13 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 15) 13 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
