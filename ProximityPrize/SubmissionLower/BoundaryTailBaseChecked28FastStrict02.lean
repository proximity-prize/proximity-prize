import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr28p16:∀ i ∈ List.range 1,StrictCheckAt 28 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 16) 28 16:=by decide +kernel
  have hfast:StrictAtFast (row 28 16) 28 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 16) 28 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 16) 28 16 hvalid hfast

theorem sr28p17:∀ i ∈ List.range 1,StrictCheckAt 28 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 17) 28 17:=by decide +kernel
  have hfast:StrictAtFast (row 28 17) 28 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 17) 28 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 17) 28 17 hvalid hfast

theorem sr28p18:∀ i ∈ List.range 1,StrictCheckAt 28 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 18) 28 18:=by decide +kernel
  have hfast:StrictAtFast (row 28 18) 28 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 18) 28 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 18) 28 18 hvalid hfast

theorem sr28p19:∀ i ∈ List.range 1,StrictCheckAt 28 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 19) 28 19:=by decide +kernel
  have hfast:StrictAtFast (row 28 19) 28 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 19) 28 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 19) 28 19 hvalid hfast

theorem sr28p20:∀ i ∈ List.range 1,StrictCheckAt 28 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 20) 28 20:=by decide +kernel
  have hfast:StrictAtFast (row 28 20) 28 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 20) 28 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 20) 28 20 hvalid hfast

theorem sr28p21:∀ i ∈ List.range 1,StrictCheckAt 28 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 21) 28 21:=by decide +kernel
  have hfast:StrictAtFast (row 28 21) 28 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 21) 28 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 21) 28 21 hvalid hfast

theorem sr28p22:∀ i ∈ List.range 1,StrictCheckAt 28 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 22) 28 22:=by decide +kernel
  have hfast:StrictAtFast (row 28 22) 28 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 22) 28 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 22) 28 22 hvalid hfast

theorem sr28p23:∀ i ∈ List.range 1,StrictCheckAt 28 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 23) 28 23:=by decide +kernel
  have hfast:StrictAtFast (row 28 23) 28 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 23) 28 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 23) 28 23 hvalid hfast

theorem sr28p24:∀ i ∈ List.range 1,StrictCheckAt 28 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 24) 28 24:=by decide +kernel
  have hfast:StrictAtFast (row 28 24) 28 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 24) 28 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 24) 28 24 hvalid hfast

theorem sr28p25:∀ i ∈ List.range 1,StrictCheckAt 28 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 25) 28 25:=by decide +kernel
  have hfast:StrictAtFast (row 28 25) 28 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 25) 28 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 25) 28 25 hvalid hfast

theorem sr28p26:∀ i ∈ List.range 1,StrictCheckAt 28 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 26) 28 26:=by decide +kernel
  have hfast:StrictAtFast (row 28 26) 28 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 26) 28 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 26) 28 26 hvalid hfast

theorem sr28p27:∀ i ∈ List.range 1,StrictCheckAt 28 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 27) 28 27:=by decide +kernel
  have hfast:StrictAtFast (row 28 27) 28 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 27) 28 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 27) 28 27 hvalid hfast

theorem sr28p28:∀ i ∈ List.range 1,StrictCheckAt 28 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 28) 28 28:=by decide +kernel
  have hfast:StrictAtFast (row 28 28) 28 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 28) 28 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 28) 28 28 hvalid hfast

theorem sr28p29:∀ i ∈ List.range 1,StrictCheckAt 28 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 29) 28 29:=by decide +kernel
  have hfast:StrictAtFast (row 28 29) 28 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 29) 28 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 29) 28 29 hvalid hfast

theorem sr28p30:∀ i ∈ List.range 1,StrictCheckAt 28 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 30) 28 30:=by decide +kernel
  have hfast:StrictAtFast (row 28 30) 28 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 30) 28 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 30) 28 30 hvalid hfast

theorem sr28p31:∀ i ∈ List.range 1,StrictCheckAt 28 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 31) 28 31:=by decide +kernel
  have hfast:StrictAtFast (row 28 31) 28 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 31) 28 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 31) 28 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
