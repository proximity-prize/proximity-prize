import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr22p16:∀ i ∈ List.range 1,StrictCheckAt 22 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 16) 22 16:=by decide +kernel
  have hfast:StrictAtFast (row 22 16) 22 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 16) 22 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 16) 22 16 hvalid hfast

theorem sr22p17:∀ i ∈ List.range 1,StrictCheckAt 22 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 17) 22 17:=by decide +kernel
  have hfast:StrictAtFast (row 22 17) 22 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 17) 22 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 17) 22 17 hvalid hfast

theorem sr22p18:∀ i ∈ List.range 1,StrictCheckAt 22 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 18) 22 18:=by decide +kernel
  have hfast:StrictAtFast (row 22 18) 22 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 18) 22 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 18) 22 18 hvalid hfast

theorem sr22p19:∀ i ∈ List.range 1,StrictCheckAt 22 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 19) 22 19:=by decide +kernel
  have hfast:StrictAtFast (row 22 19) 22 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 19) 22 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 19) 22 19 hvalid hfast

theorem sr22p20:∀ i ∈ List.range 1,StrictCheckAt 22 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 20) 22 20:=by decide +kernel
  have hfast:StrictAtFast (row 22 20) 22 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 20) 22 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 20) 22 20 hvalid hfast

theorem sr22p21:∀ i ∈ List.range 1,StrictCheckAt 22 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 21) 22 21:=by decide +kernel
  have hfast:StrictAtFast (row 22 21) 22 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 21) 22 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 21) 22 21 hvalid hfast

theorem sr22p22:∀ i ∈ List.range 1,StrictCheckAt 22 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 22) 22 22:=by decide +kernel
  have hfast:StrictAtFast (row 22 22) 22 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 22) 22 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 22) 22 22 hvalid hfast

theorem sr22p23:∀ i ∈ List.range 1,StrictCheckAt 22 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 23) 22 23:=by decide +kernel
  have hfast:StrictAtFast (row 22 23) 22 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 23) 22 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 23) 22 23 hvalid hfast

theorem sr22p24:∀ i ∈ List.range 1,StrictCheckAt 22 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 24) 22 24:=by decide +kernel
  have hfast:StrictAtFast (row 22 24) 22 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 24) 22 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 24) 22 24 hvalid hfast

theorem sr22p25:∀ i ∈ List.range 1,StrictCheckAt 22 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 25) 22 25:=by decide +kernel
  have hfast:StrictAtFast (row 22 25) 22 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 25) 22 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 25) 22 25 hvalid hfast

theorem sr22p26:∀ i ∈ List.range 1,StrictCheckAt 22 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 26) 22 26:=by decide +kernel
  have hfast:StrictAtFast (row 22 26) 22 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 26) 22 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 26) 22 26 hvalid hfast

theorem sr22p27:∀ i ∈ List.range 1,StrictCheckAt 22 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 27) 22 27:=by decide +kernel
  have hfast:StrictAtFast (row 22 27) 22 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 27) 22 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 27) 22 27 hvalid hfast

theorem sr22p28:∀ i ∈ List.range 1,StrictCheckAt 22 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 28) 22 28:=by decide +kernel
  have hfast:StrictAtFast (row 22 28) 22 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 28) 22 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 28) 22 28 hvalid hfast

theorem sr22p29:∀ i ∈ List.range 1,StrictCheckAt 22 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 29) 22 29:=by decide +kernel
  have hfast:StrictAtFast (row 22 29) 22 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 29) 22 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 29) 22 29 hvalid hfast

theorem sr22p30:∀ i ∈ List.range 1,StrictCheckAt 22 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 30) 22 30:=by decide +kernel
  have hfast:StrictAtFast (row 22 30) 22 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 30) 22 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 30) 22 30 hvalid hfast

theorem sr22p31:∀ i ∈ List.range 1,StrictCheckAt 22 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 31) 22 31:=by decide +kernel
  have hfast:StrictAtFast (row 22 31) 22 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 31) 22 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 31) 22 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
