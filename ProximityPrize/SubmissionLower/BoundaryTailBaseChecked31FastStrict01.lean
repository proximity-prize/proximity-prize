import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr31p0:∀ i ∈ List.range 1,StrictCheckAt 31 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 0) 31 0:=by decide +kernel
  have hfast:StrictAtFast (row 31 0) 31 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 0) 31 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 0) 31 0 hvalid hfast

theorem sr31p1:∀ i ∈ List.range 1,StrictCheckAt 31 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 1) 31 1:=by decide +kernel
  have hfast:StrictAtFast (row 31 1) 31 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 1) 31 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 1) 31 1 hvalid hfast

theorem sr31p2:∀ i ∈ List.range 1,StrictCheckAt 31 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 2) 31 2:=by decide +kernel
  have hfast:StrictAtFast (row 31 2) 31 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 2) 31 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 2) 31 2 hvalid hfast

theorem sr31p3:∀ i ∈ List.range 1,StrictCheckAt 31 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 3) 31 3:=by decide +kernel
  have hfast:StrictAtFast (row 31 3) 31 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 3) 31 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 3) 31 3 hvalid hfast

theorem sr31p4:∀ i ∈ List.range 1,StrictCheckAt 31 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 4) 31 4:=by decide +kernel
  have hfast:StrictAtFast (row 31 4) 31 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 4) 31 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 4) 31 4 hvalid hfast

theorem sr31p5:∀ i ∈ List.range 1,StrictCheckAt 31 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 5) 31 5:=by decide +kernel
  have hfast:StrictAtFast (row 31 5) 31 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 5) 31 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 5) 31 5 hvalid hfast

theorem sr31p6:∀ i ∈ List.range 1,StrictCheckAt 31 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 6) 31 6:=by decide +kernel
  have hfast:StrictAtFast (row 31 6) 31 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 6) 31 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 6) 31 6 hvalid hfast

theorem sr31p7:∀ i ∈ List.range 1,StrictCheckAt 31 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 7) 31 7:=by decide +kernel
  have hfast:StrictAtFast (row 31 7) 31 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 7) 31 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 7) 31 7 hvalid hfast

theorem sr31p8:∀ i ∈ List.range 1,StrictCheckAt 31 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 8) 31 8:=by decide +kernel
  have hfast:StrictAtFast (row 31 8) 31 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 8) 31 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 8) 31 8 hvalid hfast

theorem sr31p9:∀ i ∈ List.range 1,StrictCheckAt 31 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 9) 31 9:=by decide +kernel
  have hfast:StrictAtFast (row 31 9) 31 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 9) 31 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 9) 31 9 hvalid hfast

theorem sr31p10:∀ i ∈ List.range 1,StrictCheckAt 31 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 10) 31 10:=by decide +kernel
  have hfast:StrictAtFast (row 31 10) 31 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 10) 31 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 10) 31 10 hvalid hfast

theorem sr31p11:∀ i ∈ List.range 1,StrictCheckAt 31 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 11) 31 11:=by decide +kernel
  have hfast:StrictAtFast (row 31 11) 31 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 11) 31 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 11) 31 11 hvalid hfast

theorem sr31p12:∀ i ∈ List.range 1,StrictCheckAt 31 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 12) 31 12:=by decide +kernel
  have hfast:StrictAtFast (row 31 12) 31 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 12) 31 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 12) 31 12 hvalid hfast

theorem sr31p13:∀ i ∈ List.range 1,StrictCheckAt 31 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 13) 31 13:=by decide +kernel
  have hfast:StrictAtFast (row 31 13) 31 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 13) 31 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 13) 31 13 hvalid hfast

theorem sr31p14:∀ i ∈ List.range 1,StrictCheckAt 31 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 14) 31 14:=by decide +kernel
  have hfast:StrictAtFast (row 31 14) 31 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 14) 31 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 14) 31 14 hvalid hfast

theorem sr31p15:∀ i ∈ List.range 1,StrictCheckAt 31 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 15) 31 15:=by decide +kernel
  have hfast:StrictAtFast (row 31 15) 31 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 15) 31 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 15) 31 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
