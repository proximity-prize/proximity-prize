import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr21p0:∀ i ∈ List.range 1,StrictCheckAt 21 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 0) 21 0:=by decide +kernel
  have hfast:StrictAtFast (row 21 0) 21 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 0) 21 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 0) 21 0 hvalid hfast

theorem sr21p1:∀ i ∈ List.range 1,StrictCheckAt 21 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 1) 21 1:=by decide +kernel
  have hfast:StrictAtFast (row 21 1) 21 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 1) 21 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 1) 21 1 hvalid hfast

theorem sr21p2:∀ i ∈ List.range 1,StrictCheckAt 21 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 2) 21 2:=by decide +kernel
  have hfast:StrictAtFast (row 21 2) 21 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 2) 21 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 2) 21 2 hvalid hfast

theorem sr21p3:∀ i ∈ List.range 1,StrictCheckAt 21 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 3) 21 3:=by decide +kernel
  have hfast:StrictAtFast (row 21 3) 21 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 3) 21 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 3) 21 3 hvalid hfast

theorem sr21p4:∀ i ∈ List.range 1,StrictCheckAt 21 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 4) 21 4:=by decide +kernel
  have hfast:StrictAtFast (row 21 4) 21 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 4) 21 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 4) 21 4 hvalid hfast

theorem sr21p5:∀ i ∈ List.range 1,StrictCheckAt 21 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 5) 21 5:=by decide +kernel
  have hfast:StrictAtFast (row 21 5) 21 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 5) 21 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 5) 21 5 hvalid hfast

theorem sr21p6:∀ i ∈ List.range 1,StrictCheckAt 21 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 6) 21 6:=by decide +kernel
  have hfast:StrictAtFast (row 21 6) 21 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 6) 21 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 6) 21 6 hvalid hfast

theorem sr21p7:∀ i ∈ List.range 1,StrictCheckAt 21 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 7) 21 7:=by decide +kernel
  have hfast:StrictAtFast (row 21 7) 21 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 7) 21 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 7) 21 7 hvalid hfast

theorem sr21p8:∀ i ∈ List.range 1,StrictCheckAt 21 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 8) 21 8:=by decide +kernel
  have hfast:StrictAtFast (row 21 8) 21 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 8) 21 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 8) 21 8 hvalid hfast

theorem sr21p9:∀ i ∈ List.range 1,StrictCheckAt 21 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 9) 21 9:=by decide +kernel
  have hfast:StrictAtFast (row 21 9) 21 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 9) 21 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 9) 21 9 hvalid hfast

theorem sr21p10:∀ i ∈ List.range 1,StrictCheckAt 21 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 10) 21 10:=by decide +kernel
  have hfast:StrictAtFast (row 21 10) 21 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 10) 21 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 10) 21 10 hvalid hfast

theorem sr21p11:∀ i ∈ List.range 1,StrictCheckAt 21 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 11) 21 11:=by decide +kernel
  have hfast:StrictAtFast (row 21 11) 21 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 11) 21 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 11) 21 11 hvalid hfast

theorem sr21p12:∀ i ∈ List.range 1,StrictCheckAt 21 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 12) 21 12:=by decide +kernel
  have hfast:StrictAtFast (row 21 12) 21 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 12) 21 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 12) 21 12 hvalid hfast

theorem sr21p13:∀ i ∈ List.range 1,StrictCheckAt 21 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 13) 21 13:=by decide +kernel
  have hfast:StrictAtFast (row 21 13) 21 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 13) 21 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 13) 21 13 hvalid hfast

theorem sr21p14:∀ i ∈ List.range 1,StrictCheckAt 21 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 14) 21 14:=by decide +kernel
  have hfast:StrictAtFast (row 21 14) 21 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 14) 21 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 14) 21 14 hvalid hfast

theorem sr21p15:∀ i ∈ List.range 1,StrictCheckAt 21 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 15) 21 15:=by decide +kernel
  have hfast:StrictAtFast (row 21 15) 21 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 15) 21 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 15) 21 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
