import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastCorrect02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr7p0:∀ i ∈ List.range 1,StrictCheckAt 7 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 0) 7 0:=by decide +kernel
  have hfast:StrictAtFast (row 7 0) 7 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 0) 7 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 0) 7 0 hvalid hfast

theorem sr7p1:∀ i ∈ List.range 1,StrictCheckAt 7 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 1) 7 1:=by decide +kernel
  have hfast:StrictAtFast (row 7 1) 7 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 1) 7 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 1) 7 1 hvalid hfast

theorem sr7p2:∀ i ∈ List.range 1,StrictCheckAt 7 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 2) 7 2:=by decide +kernel
  have hfast:StrictAtFast (row 7 2) 7 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 2) 7 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 2) 7 2 hvalid hfast

theorem sr7p3:∀ i ∈ List.range 1,StrictCheckAt 7 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 3) 7 3:=by decide +kernel
  have hfast:StrictAtFast (row 7 3) 7 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 3) 7 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 3) 7 3 hvalid hfast

theorem sr7p4:∀ i ∈ List.range 1,StrictCheckAt 7 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 4) 7 4:=by decide +kernel
  have hfast:StrictAtFast (row 7 4) 7 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 4) 7 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 4) 7 4 hvalid hfast

theorem sr7p5:∀ i ∈ List.range 1,StrictCheckAt 7 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 5) 7 5:=by decide +kernel
  have hfast:StrictAtFast (row 7 5) 7 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 5) 7 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 5) 7 5 hvalid hfast

theorem sr7p6:∀ i ∈ List.range 1,StrictCheckAt 7 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 6) 7 6:=by decide +kernel
  have hfast:StrictAtFast (row 7 6) 7 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 6) 7 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 6) 7 6 hvalid hfast

theorem sr7p7:∀ i ∈ List.range 1,StrictCheckAt 7 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 7) 7 7:=by decide +kernel
  have hfast:StrictAtFast (row 7 7) 7 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 7) 7 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 7) 7 7 hvalid hfast

theorem sr7p8:∀ i ∈ List.range 1,StrictCheckAt 7 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 8) 7 8:=by decide +kernel
  have hfast:StrictAtFast (row 7 8) 7 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 8) 7 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 8) 7 8 hvalid hfast

theorem sr7p9:∀ i ∈ List.range 1,StrictCheckAt 7 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 9) 7 9:=by decide +kernel
  have hfast:StrictAtFast (row 7 9) 7 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 9) 7 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 9) 7 9 hvalid hfast

theorem sr7p10:∀ i ∈ List.range 1,StrictCheckAt 7 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 10) 7 10:=by decide +kernel
  have hfast:StrictAtFast (row 7 10) 7 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 10) 7 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 10) 7 10 hvalid hfast

theorem sr7p11:∀ i ∈ List.range 1,StrictCheckAt 7 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 11) 7 11:=by decide +kernel
  have hfast:StrictAtFast (row 7 11) 7 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 11) 7 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 11) 7 11 hvalid hfast

theorem sr7p12:∀ i ∈ List.range 1,StrictCheckAt 7 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 12) 7 12:=by decide +kernel
  have hfast:StrictAtFast (row 7 12) 7 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 12) 7 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 12) 7 12 hvalid hfast

theorem sr7p13:∀ i ∈ List.range 1,StrictCheckAt 7 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 13) 7 13:=by decide +kernel
  have hfast:StrictAtFast (row 7 13) 7 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 13) 7 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 13) 7 13 hvalid hfast

theorem sr7p14:∀ i ∈ List.range 1,StrictCheckAt 7 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 14) 7 14:=by decide +kernel
  have hfast:StrictAtFast (row 7 14) 7 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 14) 7 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 14) 7 14 hvalid hfast

theorem sr7p15:∀ i ∈ List.range 1,StrictCheckAt 7 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 15) 7 15:=by decide +kernel
  have hfast:StrictAtFast (row 7 15) 7 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 15) 7 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 15) 7 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
