import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr23p0:∀ i ∈ List.range 1,StrictCheckAt 23 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 0) 23 0:=by decide +kernel
  have hfast:StrictAtFast (row 23 0) 23 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 0) 23 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 0) 23 0 hvalid hfast

theorem sr23p1:∀ i ∈ List.range 1,StrictCheckAt 23 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 1) 23 1:=by decide +kernel
  have hfast:StrictAtFast (row 23 1) 23 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 1) 23 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 1) 23 1 hvalid hfast

theorem sr23p2:∀ i ∈ List.range 1,StrictCheckAt 23 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 2) 23 2:=by decide +kernel
  have hfast:StrictAtFast (row 23 2) 23 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 2) 23 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 2) 23 2 hvalid hfast

theorem sr23p3:∀ i ∈ List.range 1,StrictCheckAt 23 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 3) 23 3:=by decide +kernel
  have hfast:StrictAtFast (row 23 3) 23 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 3) 23 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 3) 23 3 hvalid hfast

theorem sr23p4:∀ i ∈ List.range 1,StrictCheckAt 23 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 4) 23 4:=by decide +kernel
  have hfast:StrictAtFast (row 23 4) 23 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 4) 23 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 4) 23 4 hvalid hfast

theorem sr23p5:∀ i ∈ List.range 1,StrictCheckAt 23 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 5) 23 5:=by decide +kernel
  have hfast:StrictAtFast (row 23 5) 23 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 5) 23 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 5) 23 5 hvalid hfast

theorem sr23p6:∀ i ∈ List.range 1,StrictCheckAt 23 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 6) 23 6:=by decide +kernel
  have hfast:StrictAtFast (row 23 6) 23 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 6) 23 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 6) 23 6 hvalid hfast

theorem sr23p7:∀ i ∈ List.range 1,StrictCheckAt 23 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 7) 23 7:=by decide +kernel
  have hfast:StrictAtFast (row 23 7) 23 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 7) 23 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 7) 23 7 hvalid hfast

theorem sr23p8:∀ i ∈ List.range 1,StrictCheckAt 23 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 8) 23 8:=by decide +kernel
  have hfast:StrictAtFast (row 23 8) 23 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 8) 23 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 8) 23 8 hvalid hfast

theorem sr23p9:∀ i ∈ List.range 1,StrictCheckAt 23 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 9) 23 9:=by decide +kernel
  have hfast:StrictAtFast (row 23 9) 23 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 9) 23 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 9) 23 9 hvalid hfast

theorem sr23p10:∀ i ∈ List.range 1,StrictCheckAt 23 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 10) 23 10:=by decide +kernel
  have hfast:StrictAtFast (row 23 10) 23 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 10) 23 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 10) 23 10 hvalid hfast

theorem sr23p11:∀ i ∈ List.range 1,StrictCheckAt 23 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 11) 23 11:=by decide +kernel
  have hfast:StrictAtFast (row 23 11) 23 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 11) 23 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 11) 23 11 hvalid hfast

theorem sr23p12:∀ i ∈ List.range 1,StrictCheckAt 23 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 12) 23 12:=by decide +kernel
  have hfast:StrictAtFast (row 23 12) 23 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 12) 23 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 12) 23 12 hvalid hfast

theorem sr23p13:∀ i ∈ List.range 1,StrictCheckAt 23 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 13) 23 13:=by decide +kernel
  have hfast:StrictAtFast (row 23 13) 23 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 13) 23 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 13) 23 13 hvalid hfast

theorem sr23p14:∀ i ∈ List.range 1,StrictCheckAt 23 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 14) 23 14:=by decide +kernel
  have hfast:StrictAtFast (row 23 14) 23 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 14) 23 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 14) 23 14 hvalid hfast

theorem sr23p15:∀ i ∈ List.range 1,StrictCheckAt 23 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 15) 23 15:=by decide +kernel
  have hfast:StrictAtFast (row 23 15) 23 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 15) 23 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 15) 23 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
