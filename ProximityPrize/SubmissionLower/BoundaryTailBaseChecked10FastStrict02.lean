import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p16:∀ i ∈ List.range 1,StrictCheckAt 10 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 16) 10 16:=by decide +kernel
  have hfast:StrictAtFast (row 10 16) 10 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 16) 10 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 16) 10 16 hvalid hfast

theorem sr10p17:∀ i ∈ List.range 1,StrictCheckAt 10 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 17) 10 17:=by decide +kernel
  have hfast:StrictAtFast (row 10 17) 10 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 17) 10 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 17) 10 17 hvalid hfast

theorem sr10p18:∀ i ∈ List.range 1,StrictCheckAt 10 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 18) 10 18:=by decide +kernel
  have hfast:StrictAtFast (row 10 18) 10 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 18) 10 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 18) 10 18 hvalid hfast

theorem sr10p19:∀ i ∈ List.range 1,StrictCheckAt 10 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 19) 10 19:=by decide +kernel
  have hfast:StrictAtFast (row 10 19) 10 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 19) 10 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 19) 10 19 hvalid hfast

theorem sr10p20:∀ i ∈ List.range 1,StrictCheckAt 10 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 20) 10 20:=by decide +kernel
  have hfast:StrictAtFast (row 10 20) 10 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 20) 10 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 20) 10 20 hvalid hfast

theorem sr10p21:∀ i ∈ List.range 1,StrictCheckAt 10 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 21) 10 21:=by decide +kernel
  have hfast:StrictAtFast (row 10 21) 10 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 21) 10 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 21) 10 21 hvalid hfast

theorem sr10p22:∀ i ∈ List.range 1,StrictCheckAt 10 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 22) 10 22:=by decide +kernel
  have hfast:StrictAtFast (row 10 22) 10 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 22) 10 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 22) 10 22 hvalid hfast

theorem sr10p23:∀ i ∈ List.range 1,StrictCheckAt 10 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 23) 10 23:=by decide +kernel
  have hfast:StrictAtFast (row 10 23) 10 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 23) 10 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 23) 10 23 hvalid hfast

theorem sr10p24:∀ i ∈ List.range 1,StrictCheckAt 10 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 24) 10 24:=by decide +kernel
  have hfast:StrictAtFast (row 10 24) 10 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 24) 10 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 24) 10 24 hvalid hfast

theorem sr10p25:∀ i ∈ List.range 1,StrictCheckAt 10 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 25) 10 25:=by decide +kernel
  have hfast:StrictAtFast (row 10 25) 10 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 25) 10 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 25) 10 25 hvalid hfast

theorem sr10p26:∀ i ∈ List.range 1,StrictCheckAt 10 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 26) 10 26:=by decide +kernel
  have hfast:StrictAtFast (row 10 26) 10 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 26) 10 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 26) 10 26 hvalid hfast

theorem sr10p27:∀ i ∈ List.range 1,StrictCheckAt 10 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 27) 10 27:=by decide +kernel
  have hfast:StrictAtFast (row 10 27) 10 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 27) 10 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 27) 10 27 hvalid hfast

theorem sr10p28:∀ i ∈ List.range 1,StrictCheckAt 10 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 28) 10 28:=by decide +kernel
  have hfast:StrictAtFast (row 10 28) 10 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 28) 10 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 28) 10 28 hvalid hfast

theorem sr10p29:∀ i ∈ List.range 1,StrictCheckAt 10 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 29) 10 29:=by decide +kernel
  have hfast:StrictAtFast (row 10 29) 10 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 29) 10 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 29) 10 29 hvalid hfast

theorem sr10p30:∀ i ∈ List.range 1,StrictCheckAt 10 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 30) 10 30:=by decide +kernel
  have hfast:StrictAtFast (row 10 30) 10 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 30) 10 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 30) 10 30 hvalid hfast

theorem sr10p31:∀ i ∈ List.range 1,StrictCheckAt 10 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 31) 10 31:=by decide +kernel
  have hfast:StrictAtFast (row 10 31) 10 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 31) 10 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 31) 10 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
