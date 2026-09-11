import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr27p0:∀ i ∈ List.range 1,StrictCheckAt 27 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 0) 27 0:=by decide +kernel
  have hfast:StrictAtFast (row 27 0) 27 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 0) 27 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 0) 27 0 hvalid hfast

theorem sr27p1:∀ i ∈ List.range 1,StrictCheckAt 27 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 1) 27 1:=by decide +kernel
  have hfast:StrictAtFast (row 27 1) 27 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 1) 27 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 1) 27 1 hvalid hfast

theorem sr27p2:∀ i ∈ List.range 1,StrictCheckAt 27 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 2) 27 2:=by decide +kernel
  have hfast:StrictAtFast (row 27 2) 27 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 2) 27 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 2) 27 2 hvalid hfast

theorem sr27p3:∀ i ∈ List.range 1,StrictCheckAt 27 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 3) 27 3:=by decide +kernel
  have hfast:StrictAtFast (row 27 3) 27 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 3) 27 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 3) 27 3 hvalid hfast

theorem sr27p4:∀ i ∈ List.range 1,StrictCheckAt 27 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 4) 27 4:=by decide +kernel
  have hfast:StrictAtFast (row 27 4) 27 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 4) 27 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 4) 27 4 hvalid hfast

theorem sr27p5:∀ i ∈ List.range 1,StrictCheckAt 27 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 5) 27 5:=by decide +kernel
  have hfast:StrictAtFast (row 27 5) 27 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 5) 27 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 5) 27 5 hvalid hfast

theorem sr27p6:∀ i ∈ List.range 1,StrictCheckAt 27 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 6) 27 6:=by decide +kernel
  have hfast:StrictAtFast (row 27 6) 27 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 6) 27 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 6) 27 6 hvalid hfast

theorem sr27p7:∀ i ∈ List.range 1,StrictCheckAt 27 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 7) 27 7:=by decide +kernel
  have hfast:StrictAtFast (row 27 7) 27 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 7) 27 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 7) 27 7 hvalid hfast

theorem sr27p8:∀ i ∈ List.range 1,StrictCheckAt 27 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 8) 27 8:=by decide +kernel
  have hfast:StrictAtFast (row 27 8) 27 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 8) 27 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 8) 27 8 hvalid hfast

theorem sr27p9:∀ i ∈ List.range 1,StrictCheckAt 27 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 9) 27 9:=by decide +kernel
  have hfast:StrictAtFast (row 27 9) 27 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 9) 27 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 9) 27 9 hvalid hfast

theorem sr27p10:∀ i ∈ List.range 1,StrictCheckAt 27 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 10) 27 10:=by decide +kernel
  have hfast:StrictAtFast (row 27 10) 27 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 10) 27 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 10) 27 10 hvalid hfast

theorem sr27p11:∀ i ∈ List.range 1,StrictCheckAt 27 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 11) 27 11:=by decide +kernel
  have hfast:StrictAtFast (row 27 11) 27 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 11) 27 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 11) 27 11 hvalid hfast

theorem sr27p12:∀ i ∈ List.range 1,StrictCheckAt 27 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 12) 27 12:=by decide +kernel
  have hfast:StrictAtFast (row 27 12) 27 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 12) 27 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 12) 27 12 hvalid hfast

theorem sr27p13:∀ i ∈ List.range 1,StrictCheckAt 27 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 13) 27 13:=by decide +kernel
  have hfast:StrictAtFast (row 27 13) 27 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 13) 27 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 13) 27 13 hvalid hfast

theorem sr27p14:∀ i ∈ List.range 1,StrictCheckAt 27 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 14) 27 14:=by decide +kernel
  have hfast:StrictAtFast (row 27 14) 27 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 14) 27 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 14) 27 14 hvalid hfast

theorem sr27p15:∀ i ∈ List.range 1,StrictCheckAt 27 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 15) 27 15:=by decide +kernel
  have hfast:StrictAtFast (row 27 15) 27 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 15) 27 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 15) 27 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
