import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr17p0:∀ i ∈ List.range 1,StrictCheckAt 17 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 0) 17 0:=by decide +kernel
  have hfast:StrictAtFast (row 17 0) 17 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 0) 17 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 0) 17 0 hvalid hfast

theorem sr17p1:∀ i ∈ List.range 1,StrictCheckAt 17 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 1) 17 1:=by decide +kernel
  have hfast:StrictAtFast (row 17 1) 17 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 1) 17 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 1) 17 1 hvalid hfast

theorem sr17p2:∀ i ∈ List.range 1,StrictCheckAt 17 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 2) 17 2:=by decide +kernel
  have hfast:StrictAtFast (row 17 2) 17 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 2) 17 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 2) 17 2 hvalid hfast

theorem sr17p3:∀ i ∈ List.range 1,StrictCheckAt 17 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 3) 17 3:=by decide +kernel
  have hfast:StrictAtFast (row 17 3) 17 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 3) 17 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 3) 17 3 hvalid hfast

theorem sr17p4:∀ i ∈ List.range 1,StrictCheckAt 17 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 4) 17 4:=by decide +kernel
  have hfast:StrictAtFast (row 17 4) 17 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 4) 17 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 4) 17 4 hvalid hfast

theorem sr17p5:∀ i ∈ List.range 1,StrictCheckAt 17 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 5) 17 5:=by decide +kernel
  have hfast:StrictAtFast (row 17 5) 17 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 5) 17 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 5) 17 5 hvalid hfast

theorem sr17p6:∀ i ∈ List.range 1,StrictCheckAt 17 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 6) 17 6:=by decide +kernel
  have hfast:StrictAtFast (row 17 6) 17 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 6) 17 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 6) 17 6 hvalid hfast

theorem sr17p7:∀ i ∈ List.range 1,StrictCheckAt 17 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 7) 17 7:=by decide +kernel
  have hfast:StrictAtFast (row 17 7) 17 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 7) 17 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 7) 17 7 hvalid hfast

theorem sr17p8:∀ i ∈ List.range 1,StrictCheckAt 17 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 8) 17 8:=by decide +kernel
  have hfast:StrictAtFast (row 17 8) 17 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 8) 17 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 8) 17 8 hvalid hfast

theorem sr17p9:∀ i ∈ List.range 1,StrictCheckAt 17 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 9) 17 9:=by decide +kernel
  have hfast:StrictAtFast (row 17 9) 17 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 9) 17 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 9) 17 9 hvalid hfast

theorem sr17p10:∀ i ∈ List.range 1,StrictCheckAt 17 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 10) 17 10:=by decide +kernel
  have hfast:StrictAtFast (row 17 10) 17 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 10) 17 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 10) 17 10 hvalid hfast

theorem sr17p11:∀ i ∈ List.range 1,StrictCheckAt 17 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 11) 17 11:=by decide +kernel
  have hfast:StrictAtFast (row 17 11) 17 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 11) 17 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 11) 17 11 hvalid hfast

theorem sr17p12:∀ i ∈ List.range 1,StrictCheckAt 17 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 12) 17 12:=by decide +kernel
  have hfast:StrictAtFast (row 17 12) 17 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 12) 17 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 12) 17 12 hvalid hfast

theorem sr17p13:∀ i ∈ List.range 1,StrictCheckAt 17 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 13) 17 13:=by decide +kernel
  have hfast:StrictAtFast (row 17 13) 17 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 13) 17 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 13) 17 13 hvalid hfast

theorem sr17p14:∀ i ∈ List.range 1,StrictCheckAt 17 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 14) 17 14:=by decide +kernel
  have hfast:StrictAtFast (row 17 14) 17 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 14) 17 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 14) 17 14 hvalid hfast

theorem sr17p15:∀ i ∈ List.range 1,StrictCheckAt 17 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 15) 17 15:=by decide +kernel
  have hfast:StrictAtFast (row 17 15) 17 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 15) 17 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 15) 17 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
