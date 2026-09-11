import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr26p16:∀ i ∈ List.range 1,StrictCheckAt 26 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 16) 26 16:=by decide +kernel
  have hfast:StrictAtFast (row 26 16) 26 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 16) 26 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 16) 26 16 hvalid hfast

theorem sr26p17:∀ i ∈ List.range 1,StrictCheckAt 26 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 17) 26 17:=by decide +kernel
  have hfast:StrictAtFast (row 26 17) 26 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 17) 26 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 17) 26 17 hvalid hfast

theorem sr26p18:∀ i ∈ List.range 1,StrictCheckAt 26 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 18) 26 18:=by decide +kernel
  have hfast:StrictAtFast (row 26 18) 26 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 18) 26 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 18) 26 18 hvalid hfast

theorem sr26p19:∀ i ∈ List.range 1,StrictCheckAt 26 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 19) 26 19:=by decide +kernel
  have hfast:StrictAtFast (row 26 19) 26 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 19) 26 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 19) 26 19 hvalid hfast

theorem sr26p20:∀ i ∈ List.range 1,StrictCheckAt 26 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 20) 26 20:=by decide +kernel
  have hfast:StrictAtFast (row 26 20) 26 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 20) 26 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 20) 26 20 hvalid hfast

theorem sr26p21:∀ i ∈ List.range 1,StrictCheckAt 26 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 21) 26 21:=by decide +kernel
  have hfast:StrictAtFast (row 26 21) 26 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 21) 26 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 21) 26 21 hvalid hfast

theorem sr26p22:∀ i ∈ List.range 1,StrictCheckAt 26 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 22) 26 22:=by decide +kernel
  have hfast:StrictAtFast (row 26 22) 26 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 22) 26 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 22) 26 22 hvalid hfast

theorem sr26p23:∀ i ∈ List.range 1,StrictCheckAt 26 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 23) 26 23:=by decide +kernel
  have hfast:StrictAtFast (row 26 23) 26 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 23) 26 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 23) 26 23 hvalid hfast

theorem sr26p24:∀ i ∈ List.range 1,StrictCheckAt 26 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 24) 26 24:=by decide +kernel
  have hfast:StrictAtFast (row 26 24) 26 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 24) 26 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 24) 26 24 hvalid hfast

theorem sr26p25:∀ i ∈ List.range 1,StrictCheckAt 26 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 25) 26 25:=by decide +kernel
  have hfast:StrictAtFast (row 26 25) 26 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 25) 26 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 25) 26 25 hvalid hfast

theorem sr26p26:∀ i ∈ List.range 1,StrictCheckAt 26 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 26) 26 26:=by decide +kernel
  have hfast:StrictAtFast (row 26 26) 26 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 26) 26 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 26) 26 26 hvalid hfast

theorem sr26p27:∀ i ∈ List.range 1,StrictCheckAt 26 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 27) 26 27:=by decide +kernel
  have hfast:StrictAtFast (row 26 27) 26 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 27) 26 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 27) 26 27 hvalid hfast

theorem sr26p28:∀ i ∈ List.range 1,StrictCheckAt 26 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 28) 26 28:=by decide +kernel
  have hfast:StrictAtFast (row 26 28) 26 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 28) 26 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 28) 26 28 hvalid hfast

theorem sr26p29:∀ i ∈ List.range 1,StrictCheckAt 26 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 29) 26 29:=by decide +kernel
  have hfast:StrictAtFast (row 26 29) 26 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 29) 26 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 29) 26 29 hvalid hfast

theorem sr26p30:∀ i ∈ List.range 1,StrictCheckAt 26 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 30) 26 30:=by decide +kernel
  have hfast:StrictAtFast (row 26 30) 26 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 30) 26 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 30) 26 30 hvalid hfast

theorem sr26p31:∀ i ∈ List.range 1,StrictCheckAt 26 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 31) 26 31:=by decide +kernel
  have hfast:StrictAtFast (row 26 31) 26 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 31) 26 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 31) 26 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
