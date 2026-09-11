import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr29p0:∀ i ∈ List.range 1,StrictCheckAt 29 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 0) 29 0:=by decide +kernel
  have hfast:StrictAtFast (row 29 0) 29 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 0) 29 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 0) 29 0 hvalid hfast

theorem sr29p1:∀ i ∈ List.range 1,StrictCheckAt 29 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 1) 29 1:=by decide +kernel
  have hfast:StrictAtFast (row 29 1) 29 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 1) 29 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 1) 29 1 hvalid hfast

theorem sr29p2:∀ i ∈ List.range 1,StrictCheckAt 29 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 2) 29 2:=by decide +kernel
  have hfast:StrictAtFast (row 29 2) 29 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 2) 29 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 2) 29 2 hvalid hfast

theorem sr29p3:∀ i ∈ List.range 1,StrictCheckAt 29 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 3) 29 3:=by decide +kernel
  have hfast:StrictAtFast (row 29 3) 29 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 3) 29 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 3) 29 3 hvalid hfast

theorem sr29p4:∀ i ∈ List.range 1,StrictCheckAt 29 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 4) 29 4:=by decide +kernel
  have hfast:StrictAtFast (row 29 4) 29 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 4) 29 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 4) 29 4 hvalid hfast

theorem sr29p5:∀ i ∈ List.range 1,StrictCheckAt 29 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 5) 29 5:=by decide +kernel
  have hfast:StrictAtFast (row 29 5) 29 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 5) 29 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 5) 29 5 hvalid hfast

theorem sr29p6:∀ i ∈ List.range 1,StrictCheckAt 29 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 6) 29 6:=by decide +kernel
  have hfast:StrictAtFast (row 29 6) 29 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 6) 29 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 6) 29 6 hvalid hfast

theorem sr29p7:∀ i ∈ List.range 1,StrictCheckAt 29 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 7) 29 7:=by decide +kernel
  have hfast:StrictAtFast (row 29 7) 29 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 7) 29 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 7) 29 7 hvalid hfast

theorem sr29p8:∀ i ∈ List.range 1,StrictCheckAt 29 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 8) 29 8:=by decide +kernel
  have hfast:StrictAtFast (row 29 8) 29 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 8) 29 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 8) 29 8 hvalid hfast

theorem sr29p9:∀ i ∈ List.range 1,StrictCheckAt 29 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 9) 29 9:=by decide +kernel
  have hfast:StrictAtFast (row 29 9) 29 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 9) 29 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 9) 29 9 hvalid hfast

theorem sr29p10:∀ i ∈ List.range 1,StrictCheckAt 29 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 10) 29 10:=by decide +kernel
  have hfast:StrictAtFast (row 29 10) 29 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 10) 29 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 10) 29 10 hvalid hfast

theorem sr29p11:∀ i ∈ List.range 1,StrictCheckAt 29 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 11) 29 11:=by decide +kernel
  have hfast:StrictAtFast (row 29 11) 29 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 11) 29 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 11) 29 11 hvalid hfast

theorem sr29p12:∀ i ∈ List.range 1,StrictCheckAt 29 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 12) 29 12:=by decide +kernel
  have hfast:StrictAtFast (row 29 12) 29 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 12) 29 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 12) 29 12 hvalid hfast

theorem sr29p13:∀ i ∈ List.range 1,StrictCheckAt 29 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 13) 29 13:=by decide +kernel
  have hfast:StrictAtFast (row 29 13) 29 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 13) 29 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 13) 29 13 hvalid hfast

theorem sr29p14:∀ i ∈ List.range 1,StrictCheckAt 29 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 14) 29 14:=by decide +kernel
  have hfast:StrictAtFast (row 29 14) 29 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 14) 29 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 14) 29 14 hvalid hfast

theorem sr29p15:∀ i ∈ List.range 1,StrictCheckAt 29 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 15) 29 15:=by decide +kernel
  have hfast:StrictAtFast (row 29 15) 29 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 15) 29 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 15) 29 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
