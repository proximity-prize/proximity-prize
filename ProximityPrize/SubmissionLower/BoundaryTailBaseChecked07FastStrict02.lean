import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr7p16:∀ i ∈ List.range 1,StrictCheckAt 7 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 16) 7 16:=by decide +kernel
  have hfast:StrictAtFast (row 7 16) 7 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 16) 7 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 16) 7 16 hvalid hfast

theorem sr7p17:∀ i ∈ List.range 1,StrictCheckAt 7 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 17) 7 17:=by decide +kernel
  have hfast:StrictAtFast (row 7 17) 7 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 17) 7 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 17) 7 17 hvalid hfast

theorem sr7p18:∀ i ∈ List.range 1,StrictCheckAt 7 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 18) 7 18:=by decide +kernel
  have hfast:StrictAtFast (row 7 18) 7 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 18) 7 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 18) 7 18 hvalid hfast

theorem sr7p19:∀ i ∈ List.range 1,StrictCheckAt 7 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 19) 7 19:=by decide +kernel
  have hfast:StrictAtFast (row 7 19) 7 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 19) 7 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 19) 7 19 hvalid hfast

theorem sr7p20:∀ i ∈ List.range 1,StrictCheckAt 7 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 20) 7 20:=by decide +kernel
  have hfast:StrictAtFast (row 7 20) 7 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 20) 7 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 20) 7 20 hvalid hfast

theorem sr7p21:∀ i ∈ List.range 1,StrictCheckAt 7 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 21) 7 21:=by decide +kernel
  have hfast:StrictAtFast (row 7 21) 7 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 21) 7 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 21) 7 21 hvalid hfast

theorem sr7p22:∀ i ∈ List.range 1,StrictCheckAt 7 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 22) 7 22:=by decide +kernel
  have hfast:StrictAtFast (row 7 22) 7 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 22) 7 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 22) 7 22 hvalid hfast

theorem sr7p23:∀ i ∈ List.range 1,StrictCheckAt 7 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 23) 7 23:=by decide +kernel
  have hfast:StrictAtFast (row 7 23) 7 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 23) 7 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 23) 7 23 hvalid hfast

theorem sr7p24:∀ i ∈ List.range 1,StrictCheckAt 7 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 24) 7 24:=by decide +kernel
  have hfast:StrictAtFast (row 7 24) 7 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 24) 7 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 24) 7 24 hvalid hfast

theorem sr7p25:∀ i ∈ List.range 1,StrictCheckAt 7 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 25) 7 25:=by decide +kernel
  have hfast:StrictAtFast (row 7 25) 7 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 25) 7 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 25) 7 25 hvalid hfast

theorem sr7p26:∀ i ∈ List.range 1,StrictCheckAt 7 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 26) 7 26:=by decide +kernel
  have hfast:StrictAtFast (row 7 26) 7 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 26) 7 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 26) 7 26 hvalid hfast

theorem sr7p27:∀ i ∈ List.range 1,StrictCheckAt 7 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 27) 7 27:=by decide +kernel
  have hfast:StrictAtFast (row 7 27) 7 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 27) 7 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 27) 7 27 hvalid hfast

theorem sr7p28:∀ i ∈ List.range 1,StrictCheckAt 7 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 28) 7 28:=by decide +kernel
  have hfast:StrictAtFast (row 7 28) 7 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 28) 7 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 28) 7 28 hvalid hfast

theorem sr7p29:∀ i ∈ List.range 1,StrictCheckAt 7 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 29) 7 29:=by decide +kernel
  have hfast:StrictAtFast (row 7 29) 7 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 29) 7 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 29) 7 29 hvalid hfast

theorem sr7p30:∀ i ∈ List.range 1,StrictCheckAt 7 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 30) 7 30:=by decide +kernel
  have hfast:StrictAtFast (row 7 30) 7 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 30) 7 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 30) 7 30 hvalid hfast

theorem sr7p31:∀ i ∈ List.range 1,StrictCheckAt 7 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 31) 7 31:=by decide +kernel
  have hfast:StrictAtFast (row 7 31) 7 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 31) 7 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 31) 7 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
