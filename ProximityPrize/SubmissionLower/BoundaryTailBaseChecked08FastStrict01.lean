import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr8p0:∀ i ∈ List.range 1,StrictCheckAt 8 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 0) 8 0:=by decide +kernel
  have hfast:StrictAtFast (row 8 0) 8 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 0) 8 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 0) 8 0 hvalid hfast

theorem sr8p1:∀ i ∈ List.range 1,StrictCheckAt 8 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 1) 8 1:=by decide +kernel
  have hfast:StrictAtFast (row 8 1) 8 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 1) 8 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 1) 8 1 hvalid hfast

theorem sr8p2:∀ i ∈ List.range 1,StrictCheckAt 8 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 2) 8 2:=by decide +kernel
  have hfast:StrictAtFast (row 8 2) 8 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 2) 8 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 2) 8 2 hvalid hfast

theorem sr8p3:∀ i ∈ List.range 1,StrictCheckAt 8 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 3) 8 3:=by decide +kernel
  have hfast:StrictAtFast (row 8 3) 8 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 3) 8 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 3) 8 3 hvalid hfast

theorem sr8p4:∀ i ∈ List.range 1,StrictCheckAt 8 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 4) 8 4:=by decide +kernel
  have hfast:StrictAtFast (row 8 4) 8 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 4) 8 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 4) 8 4 hvalid hfast

theorem sr8p5:∀ i ∈ List.range 1,StrictCheckAt 8 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 5) 8 5:=by decide +kernel
  have hfast:StrictAtFast (row 8 5) 8 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 5) 8 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 5) 8 5 hvalid hfast

theorem sr8p6:∀ i ∈ List.range 1,StrictCheckAt 8 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 6) 8 6:=by decide +kernel
  have hfast:StrictAtFast (row 8 6) 8 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 6) 8 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 6) 8 6 hvalid hfast

theorem sr8p7:∀ i ∈ List.range 1,StrictCheckAt 8 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 7) 8 7:=by decide +kernel
  have hfast:StrictAtFast (row 8 7) 8 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 7) 8 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 7) 8 7 hvalid hfast

theorem sr8p8:∀ i ∈ List.range 1,StrictCheckAt 8 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 8) 8 8:=by decide +kernel
  have hfast:StrictAtFast (row 8 8) 8 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 8) 8 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 8) 8 8 hvalid hfast

theorem sr8p9:∀ i ∈ List.range 1,StrictCheckAt 8 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 9) 8 9:=by decide +kernel
  have hfast:StrictAtFast (row 8 9) 8 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 9) 8 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 9) 8 9 hvalid hfast

theorem sr8p10:∀ i ∈ List.range 1,StrictCheckAt 8 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 10) 8 10:=by decide +kernel
  have hfast:StrictAtFast (row 8 10) 8 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 10) 8 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 10) 8 10 hvalid hfast

theorem sr8p11:∀ i ∈ List.range 1,StrictCheckAt 8 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 11) 8 11:=by decide +kernel
  have hfast:StrictAtFast (row 8 11) 8 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 11) 8 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 11) 8 11 hvalid hfast

theorem sr8p12:∀ i ∈ List.range 1,StrictCheckAt 8 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 12) 8 12:=by decide +kernel
  have hfast:StrictAtFast (row 8 12) 8 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 12) 8 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 12) 8 12 hvalid hfast

theorem sr8p13:∀ i ∈ List.range 1,StrictCheckAt 8 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 13) 8 13:=by decide +kernel
  have hfast:StrictAtFast (row 8 13) 8 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 13) 8 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 13) 8 13 hvalid hfast

theorem sr8p14:∀ i ∈ List.range 1,StrictCheckAt 8 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 14) 8 14:=by decide +kernel
  have hfast:StrictAtFast (row 8 14) 8 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 14) 8 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 14) 8 14 hvalid hfast

theorem sr8p15:∀ i ∈ List.range 1,StrictCheckAt 8 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 15) 8 15:=by decide +kernel
  have hfast:StrictAtFast (row 8 15) 8 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 15) 8 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 15) 8 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
