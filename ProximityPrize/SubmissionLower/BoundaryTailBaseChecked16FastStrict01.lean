import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr16p0:∀ i ∈ List.range 1,StrictCheckAt 16 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 0) 16 0:=by decide +kernel
  have hfast:StrictAtFast (row 16 0) 16 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 0) 16 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 0) 16 0 hvalid hfast

theorem sr16p1:∀ i ∈ List.range 1,StrictCheckAt 16 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 1) 16 1:=by decide +kernel
  have hfast:StrictAtFast (row 16 1) 16 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 1) 16 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 1) 16 1 hvalid hfast

theorem sr16p2:∀ i ∈ List.range 1,StrictCheckAt 16 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 2) 16 2:=by decide +kernel
  have hfast:StrictAtFast (row 16 2) 16 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 2) 16 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 2) 16 2 hvalid hfast

theorem sr16p3:∀ i ∈ List.range 1,StrictCheckAt 16 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 3) 16 3:=by decide +kernel
  have hfast:StrictAtFast (row 16 3) 16 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 3) 16 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 3) 16 3 hvalid hfast

theorem sr16p4:∀ i ∈ List.range 1,StrictCheckAt 16 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 4) 16 4:=by decide +kernel
  have hfast:StrictAtFast (row 16 4) 16 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 4) 16 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 4) 16 4 hvalid hfast

theorem sr16p5:∀ i ∈ List.range 1,StrictCheckAt 16 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 5) 16 5:=by decide +kernel
  have hfast:StrictAtFast (row 16 5) 16 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 5) 16 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 5) 16 5 hvalid hfast

theorem sr16p6:∀ i ∈ List.range 1,StrictCheckAt 16 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 6) 16 6:=by decide +kernel
  have hfast:StrictAtFast (row 16 6) 16 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 6) 16 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 6) 16 6 hvalid hfast

theorem sr16p7:∀ i ∈ List.range 1,StrictCheckAt 16 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 7) 16 7:=by decide +kernel
  have hfast:StrictAtFast (row 16 7) 16 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 7) 16 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 7) 16 7 hvalid hfast

theorem sr16p8:∀ i ∈ List.range 1,StrictCheckAt 16 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 8) 16 8:=by decide +kernel
  have hfast:StrictAtFast (row 16 8) 16 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 8) 16 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 8) 16 8 hvalid hfast

theorem sr16p9:∀ i ∈ List.range 1,StrictCheckAt 16 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 9) 16 9:=by decide +kernel
  have hfast:StrictAtFast (row 16 9) 16 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 9) 16 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 9) 16 9 hvalid hfast

theorem sr16p10:∀ i ∈ List.range 1,StrictCheckAt 16 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 10) 16 10:=by decide +kernel
  have hfast:StrictAtFast (row 16 10) 16 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 10) 16 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 10) 16 10 hvalid hfast

theorem sr16p11:∀ i ∈ List.range 1,StrictCheckAt 16 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 11) 16 11:=by decide +kernel
  have hfast:StrictAtFast (row 16 11) 16 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 11) 16 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 11) 16 11 hvalid hfast

theorem sr16p12:∀ i ∈ List.range 1,StrictCheckAt 16 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 12) 16 12:=by decide +kernel
  have hfast:StrictAtFast (row 16 12) 16 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 12) 16 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 12) 16 12 hvalid hfast

theorem sr16p13:∀ i ∈ List.range 1,StrictCheckAt 16 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 13) 16 13:=by decide +kernel
  have hfast:StrictAtFast (row 16 13) 16 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 13) 16 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 13) 16 13 hvalid hfast

theorem sr16p14:∀ i ∈ List.range 1,StrictCheckAt 16 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 14) 16 14:=by decide +kernel
  have hfast:StrictAtFast (row 16 14) 16 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 14) 16 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 14) 16 14 hvalid hfast

theorem sr16p15:∀ i ∈ List.range 1,StrictCheckAt 16 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 15) 16 15:=by decide +kernel
  have hfast:StrictAtFast (row 16 15) 16 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 15) 16 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 15) 16 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
