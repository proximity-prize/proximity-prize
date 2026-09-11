import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr25p0:∀ i ∈ List.range 1,StrictCheckAt 25 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 0) 25 0:=by decide +kernel
  have hfast:StrictAtFast (row 25 0) 25 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 0) 25 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 0) 25 0 hvalid hfast

theorem sr25p1:∀ i ∈ List.range 1,StrictCheckAt 25 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 1) 25 1:=by decide +kernel
  have hfast:StrictAtFast (row 25 1) 25 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 1) 25 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 1) 25 1 hvalid hfast

theorem sr25p2:∀ i ∈ List.range 1,StrictCheckAt 25 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 2) 25 2:=by decide +kernel
  have hfast:StrictAtFast (row 25 2) 25 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 2) 25 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 2) 25 2 hvalid hfast

theorem sr25p3:∀ i ∈ List.range 1,StrictCheckAt 25 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 3) 25 3:=by decide +kernel
  have hfast:StrictAtFast (row 25 3) 25 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 3) 25 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 3) 25 3 hvalid hfast

theorem sr25p4:∀ i ∈ List.range 1,StrictCheckAt 25 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 4) 25 4:=by decide +kernel
  have hfast:StrictAtFast (row 25 4) 25 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 4) 25 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 4) 25 4 hvalid hfast

theorem sr25p5:∀ i ∈ List.range 1,StrictCheckAt 25 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 5) 25 5:=by decide +kernel
  have hfast:StrictAtFast (row 25 5) 25 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 5) 25 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 5) 25 5 hvalid hfast

theorem sr25p6:∀ i ∈ List.range 1,StrictCheckAt 25 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 6) 25 6:=by decide +kernel
  have hfast:StrictAtFast (row 25 6) 25 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 6) 25 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 6) 25 6 hvalid hfast

theorem sr25p7:∀ i ∈ List.range 1,StrictCheckAt 25 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 7) 25 7:=by decide +kernel
  have hfast:StrictAtFast (row 25 7) 25 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 7) 25 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 7) 25 7 hvalid hfast

theorem sr25p8:∀ i ∈ List.range 1,StrictCheckAt 25 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 8) 25 8:=by decide +kernel
  have hfast:StrictAtFast (row 25 8) 25 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 8) 25 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 8) 25 8 hvalid hfast

theorem sr25p9:∀ i ∈ List.range 1,StrictCheckAt 25 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 9) 25 9:=by decide +kernel
  have hfast:StrictAtFast (row 25 9) 25 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 9) 25 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 9) 25 9 hvalid hfast

theorem sr25p10:∀ i ∈ List.range 1,StrictCheckAt 25 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 10) 25 10:=by decide +kernel
  have hfast:StrictAtFast (row 25 10) 25 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 10) 25 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 10) 25 10 hvalid hfast

theorem sr25p11:∀ i ∈ List.range 1,StrictCheckAt 25 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 11) 25 11:=by decide +kernel
  have hfast:StrictAtFast (row 25 11) 25 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 11) 25 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 11) 25 11 hvalid hfast

theorem sr25p12:∀ i ∈ List.range 1,StrictCheckAt 25 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 12) 25 12:=by decide +kernel
  have hfast:StrictAtFast (row 25 12) 25 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 12) 25 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 12) 25 12 hvalid hfast

theorem sr25p13:∀ i ∈ List.range 1,StrictCheckAt 25 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 13) 25 13:=by decide +kernel
  have hfast:StrictAtFast (row 25 13) 25 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 13) 25 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 13) 25 13 hvalid hfast

theorem sr25p14:∀ i ∈ List.range 1,StrictCheckAt 25 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 14) 25 14:=by decide +kernel
  have hfast:StrictAtFast (row 25 14) 25 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 14) 25 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 14) 25 14 hvalid hfast

theorem sr25p15:∀ i ∈ List.range 1,StrictCheckAt 25 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 15) 25 15:=by decide +kernel
  have hfast:StrictAtFast (row 25 15) 25 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 15) 25 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 15) 25 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
