import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr21p16:∀ i ∈ List.range 1,StrictCheckAt 21 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 16) 21 16:=by decide +kernel
  have hfast:StrictAtFast (row 21 16) 21 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 16) 21 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 16) 21 16 hvalid hfast

theorem sr21p17:∀ i ∈ List.range 1,StrictCheckAt 21 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 17) 21 17:=by decide +kernel
  have hfast:StrictAtFast (row 21 17) 21 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 17) 21 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 17) 21 17 hvalid hfast

theorem sr21p18:∀ i ∈ List.range 1,StrictCheckAt 21 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 18) 21 18:=by decide +kernel
  have hfast:StrictAtFast (row 21 18) 21 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 18) 21 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 18) 21 18 hvalid hfast

theorem sr21p19:∀ i ∈ List.range 1,StrictCheckAt 21 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 19) 21 19:=by decide +kernel
  have hfast:StrictAtFast (row 21 19) 21 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 19) 21 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 19) 21 19 hvalid hfast

theorem sr21p20:∀ i ∈ List.range 1,StrictCheckAt 21 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 20) 21 20:=by decide +kernel
  have hfast:StrictAtFast (row 21 20) 21 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 20) 21 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 20) 21 20 hvalid hfast

theorem sr21p21:∀ i ∈ List.range 1,StrictCheckAt 21 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 21) 21 21:=by decide +kernel
  have hfast:StrictAtFast (row 21 21) 21 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 21) 21 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 21) 21 21 hvalid hfast

theorem sr21p22:∀ i ∈ List.range 1,StrictCheckAt 21 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 22) 21 22:=by decide +kernel
  have hfast:StrictAtFast (row 21 22) 21 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 22) 21 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 22) 21 22 hvalid hfast

theorem sr21p23:∀ i ∈ List.range 1,StrictCheckAt 21 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 23) 21 23:=by decide +kernel
  have hfast:StrictAtFast (row 21 23) 21 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 23) 21 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 23) 21 23 hvalid hfast

theorem sr21p24:∀ i ∈ List.range 1,StrictCheckAt 21 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 24) 21 24:=by decide +kernel
  have hfast:StrictAtFast (row 21 24) 21 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 24) 21 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 24) 21 24 hvalid hfast

theorem sr21p25:∀ i ∈ List.range 1,StrictCheckAt 21 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 25) 21 25:=by decide +kernel
  have hfast:StrictAtFast (row 21 25) 21 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 25) 21 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 25) 21 25 hvalid hfast

theorem sr21p26:∀ i ∈ List.range 1,StrictCheckAt 21 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 26) 21 26:=by decide +kernel
  have hfast:StrictAtFast (row 21 26) 21 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 26) 21 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 26) 21 26 hvalid hfast

theorem sr21p27:∀ i ∈ List.range 1,StrictCheckAt 21 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 27) 21 27:=by decide +kernel
  have hfast:StrictAtFast (row 21 27) 21 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 27) 21 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 27) 21 27 hvalid hfast

theorem sr21p28:∀ i ∈ List.range 1,StrictCheckAt 21 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 28) 21 28:=by decide +kernel
  have hfast:StrictAtFast (row 21 28) 21 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 28) 21 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 28) 21 28 hvalid hfast

theorem sr21p29:∀ i ∈ List.range 1,StrictCheckAt 21 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 29) 21 29:=by decide +kernel
  have hfast:StrictAtFast (row 21 29) 21 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 29) 21 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 29) 21 29 hvalid hfast

theorem sr21p30:∀ i ∈ List.range 1,StrictCheckAt 21 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 30) 21 30:=by decide +kernel
  have hfast:StrictAtFast (row 21 30) 21 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 30) 21 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 30) 21 30 hvalid hfast

theorem sr21p31:∀ i ∈ List.range 1,StrictCheckAt 21 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 31) 21 31:=by decide +kernel
  have hfast:StrictAtFast (row 21 31) 21 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 31) 21 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 31) 21 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
