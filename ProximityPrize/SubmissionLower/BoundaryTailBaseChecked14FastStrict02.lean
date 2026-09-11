import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p16:∀ i ∈ List.range 1,StrictCheckAt 14 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 16) 14 16:=by decide +kernel
  have hfast:StrictAtFast (row 14 16) 14 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 16) 14 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 16) 14 16 hvalid hfast

theorem sr14p17:∀ i ∈ List.range 1,StrictCheckAt 14 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 17) 14 17:=by decide +kernel
  have hfast:StrictAtFast (row 14 17) 14 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 17) 14 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 17) 14 17 hvalid hfast

theorem sr14p18:∀ i ∈ List.range 1,StrictCheckAt 14 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 18) 14 18:=by decide +kernel
  have hfast:StrictAtFast (row 14 18) 14 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 18) 14 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 18) 14 18 hvalid hfast

theorem sr14p19:∀ i ∈ List.range 1,StrictCheckAt 14 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 19) 14 19:=by decide +kernel
  have hfast:StrictAtFast (row 14 19) 14 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 19) 14 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 19) 14 19 hvalid hfast

theorem sr14p20:∀ i ∈ List.range 1,StrictCheckAt 14 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 20) 14 20:=by decide +kernel
  have hfast:StrictAtFast (row 14 20) 14 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 20) 14 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 20) 14 20 hvalid hfast

theorem sr14p21:∀ i ∈ List.range 1,StrictCheckAt 14 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 21) 14 21:=by decide +kernel
  have hfast:StrictAtFast (row 14 21) 14 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 21) 14 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 21) 14 21 hvalid hfast

theorem sr14p22:∀ i ∈ List.range 1,StrictCheckAt 14 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 22) 14 22:=by decide +kernel
  have hfast:StrictAtFast (row 14 22) 14 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 22) 14 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 22) 14 22 hvalid hfast

theorem sr14p23:∀ i ∈ List.range 1,StrictCheckAt 14 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 23) 14 23:=by decide +kernel
  have hfast:StrictAtFast (row 14 23) 14 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 23) 14 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 23) 14 23 hvalid hfast

theorem sr14p24:∀ i ∈ List.range 1,StrictCheckAt 14 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 24) 14 24:=by decide +kernel
  have hfast:StrictAtFast (row 14 24) 14 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 24) 14 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 24) 14 24 hvalid hfast

theorem sr14p25:∀ i ∈ List.range 1,StrictCheckAt 14 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 25) 14 25:=by decide +kernel
  have hfast:StrictAtFast (row 14 25) 14 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 25) 14 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 25) 14 25 hvalid hfast

theorem sr14p26:∀ i ∈ List.range 1,StrictCheckAt 14 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 26) 14 26:=by decide +kernel
  have hfast:StrictAtFast (row 14 26) 14 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 26) 14 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 26) 14 26 hvalid hfast

theorem sr14p27:∀ i ∈ List.range 1,StrictCheckAt 14 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 27) 14 27:=by decide +kernel
  have hfast:StrictAtFast (row 14 27) 14 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 27) 14 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 27) 14 27 hvalid hfast

theorem sr14p28:∀ i ∈ List.range 1,StrictCheckAt 14 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 28) 14 28:=by decide +kernel
  have hfast:StrictAtFast (row 14 28) 14 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 28) 14 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 28) 14 28 hvalid hfast

theorem sr14p29:∀ i ∈ List.range 1,StrictCheckAt 14 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 29) 14 29:=by decide +kernel
  have hfast:StrictAtFast (row 14 29) 14 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 29) 14 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 29) 14 29 hvalid hfast

theorem sr14p30:∀ i ∈ List.range 1,StrictCheckAt 14 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 30) 14 30:=by decide +kernel
  have hfast:StrictAtFast (row 14 30) 14 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 30) 14 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 30) 14 30 hvalid hfast

theorem sr14p31:∀ i ∈ List.range 1,StrictCheckAt 14 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 31) 14 31:=by decide +kernel
  have hfast:StrictAtFast (row 14 31) 14 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 31) 14 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 31) 14 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
