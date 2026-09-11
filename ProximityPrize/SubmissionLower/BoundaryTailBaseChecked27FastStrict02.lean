import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr27p16:∀ i ∈ List.range 1,StrictCheckAt 27 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 16) 27 16:=by decide +kernel
  have hfast:StrictAtFast (row 27 16) 27 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 16) 27 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 16) 27 16 hvalid hfast

theorem sr27p17:∀ i ∈ List.range 1,StrictCheckAt 27 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 17) 27 17:=by decide +kernel
  have hfast:StrictAtFast (row 27 17) 27 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 17) 27 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 17) 27 17 hvalid hfast

theorem sr27p18:∀ i ∈ List.range 1,StrictCheckAt 27 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 18) 27 18:=by decide +kernel
  have hfast:StrictAtFast (row 27 18) 27 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 18) 27 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 18) 27 18 hvalid hfast

theorem sr27p19:∀ i ∈ List.range 1,StrictCheckAt 27 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 19) 27 19:=by decide +kernel
  have hfast:StrictAtFast (row 27 19) 27 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 19) 27 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 19) 27 19 hvalid hfast

theorem sr27p20:∀ i ∈ List.range 1,StrictCheckAt 27 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 20) 27 20:=by decide +kernel
  have hfast:StrictAtFast (row 27 20) 27 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 20) 27 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 20) 27 20 hvalid hfast

theorem sr27p21:∀ i ∈ List.range 1,StrictCheckAt 27 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 21) 27 21:=by decide +kernel
  have hfast:StrictAtFast (row 27 21) 27 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 21) 27 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 21) 27 21 hvalid hfast

theorem sr27p22:∀ i ∈ List.range 1,StrictCheckAt 27 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 22) 27 22:=by decide +kernel
  have hfast:StrictAtFast (row 27 22) 27 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 22) 27 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 22) 27 22 hvalid hfast

theorem sr27p23:∀ i ∈ List.range 1,StrictCheckAt 27 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 23) 27 23:=by decide +kernel
  have hfast:StrictAtFast (row 27 23) 27 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 23) 27 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 23) 27 23 hvalid hfast

theorem sr27p24:∀ i ∈ List.range 1,StrictCheckAt 27 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 24) 27 24:=by decide +kernel
  have hfast:StrictAtFast (row 27 24) 27 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 24) 27 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 24) 27 24 hvalid hfast

theorem sr27p25:∀ i ∈ List.range 1,StrictCheckAt 27 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 25) 27 25:=by decide +kernel
  have hfast:StrictAtFast (row 27 25) 27 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 25) 27 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 25) 27 25 hvalid hfast

theorem sr27p26:∀ i ∈ List.range 1,StrictCheckAt 27 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 26) 27 26:=by decide +kernel
  have hfast:StrictAtFast (row 27 26) 27 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 26) 27 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 26) 27 26 hvalid hfast

theorem sr27p27:∀ i ∈ List.range 1,StrictCheckAt 27 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 27) 27 27:=by decide +kernel
  have hfast:StrictAtFast (row 27 27) 27 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 27) 27 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 27) 27 27 hvalid hfast

theorem sr27p28:∀ i ∈ List.range 1,StrictCheckAt 27 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 28) 27 28:=by decide +kernel
  have hfast:StrictAtFast (row 27 28) 27 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 28) 27 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 28) 27 28 hvalid hfast

theorem sr27p29:∀ i ∈ List.range 1,StrictCheckAt 27 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 29) 27 29:=by decide +kernel
  have hfast:StrictAtFast (row 27 29) 27 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 29) 27 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 29) 27 29 hvalid hfast

theorem sr27p30:∀ i ∈ List.range 1,StrictCheckAt 27 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 30) 27 30:=by decide +kernel
  have hfast:StrictAtFast (row 27 30) 27 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 30) 27 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 30) 27 30 hvalid hfast

theorem sr27p31:∀ i ∈ List.range 1,StrictCheckAt 27 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 31) 27 31:=by decide +kernel
  have hfast:StrictAtFast (row 27 31) 27 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 31) 27 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 31) 27 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
