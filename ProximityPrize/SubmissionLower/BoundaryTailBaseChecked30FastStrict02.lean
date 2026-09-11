import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr30p16:∀ i ∈ List.range 1,StrictCheckAt 30 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 16) 30 16:=by decide +kernel
  have hfast:StrictAtFast (row 30 16) 30 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 16) 30 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 16) 30 16 hvalid hfast

theorem sr30p17:∀ i ∈ List.range 1,StrictCheckAt 30 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 17) 30 17:=by decide +kernel
  have hfast:StrictAtFast (row 30 17) 30 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 17) 30 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 17) 30 17 hvalid hfast

theorem sr30p18:∀ i ∈ List.range 1,StrictCheckAt 30 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 18) 30 18:=by decide +kernel
  have hfast:StrictAtFast (row 30 18) 30 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 18) 30 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 18) 30 18 hvalid hfast

theorem sr30p19:∀ i ∈ List.range 1,StrictCheckAt 30 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 19) 30 19:=by decide +kernel
  have hfast:StrictAtFast (row 30 19) 30 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 19) 30 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 19) 30 19 hvalid hfast

theorem sr30p20:∀ i ∈ List.range 1,StrictCheckAt 30 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 20) 30 20:=by decide +kernel
  have hfast:StrictAtFast (row 30 20) 30 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 20) 30 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 20) 30 20 hvalid hfast

theorem sr30p21:∀ i ∈ List.range 1,StrictCheckAt 30 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 21) 30 21:=by decide +kernel
  have hfast:StrictAtFast (row 30 21) 30 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 21) 30 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 21) 30 21 hvalid hfast

theorem sr30p22:∀ i ∈ List.range 1,StrictCheckAt 30 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 22) 30 22:=by decide +kernel
  have hfast:StrictAtFast (row 30 22) 30 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 22) 30 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 22) 30 22 hvalid hfast

theorem sr30p23:∀ i ∈ List.range 1,StrictCheckAt 30 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 23) 30 23:=by decide +kernel
  have hfast:StrictAtFast (row 30 23) 30 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 23) 30 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 23) 30 23 hvalid hfast

theorem sr30p24:∀ i ∈ List.range 1,StrictCheckAt 30 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 24) 30 24:=by decide +kernel
  have hfast:StrictAtFast (row 30 24) 30 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 24) 30 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 24) 30 24 hvalid hfast

theorem sr30p25:∀ i ∈ List.range 1,StrictCheckAt 30 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 25) 30 25:=by decide +kernel
  have hfast:StrictAtFast (row 30 25) 30 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 25) 30 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 25) 30 25 hvalid hfast

theorem sr30p26:∀ i ∈ List.range 1,StrictCheckAt 30 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 26) 30 26:=by decide +kernel
  have hfast:StrictAtFast (row 30 26) 30 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 26) 30 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 26) 30 26 hvalid hfast

theorem sr30p27:∀ i ∈ List.range 1,StrictCheckAt 30 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 27) 30 27:=by decide +kernel
  have hfast:StrictAtFast (row 30 27) 30 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 27) 30 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 27) 30 27 hvalid hfast

theorem sr30p28:∀ i ∈ List.range 1,StrictCheckAt 30 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 28) 30 28:=by decide +kernel
  have hfast:StrictAtFast (row 30 28) 30 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 28) 30 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 28) 30 28 hvalid hfast

theorem sr30p29:∀ i ∈ List.range 1,StrictCheckAt 30 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 29) 30 29:=by decide +kernel
  have hfast:StrictAtFast (row 30 29) 30 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 29) 30 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 29) 30 29 hvalid hfast

theorem sr30p30:∀ i ∈ List.range 1,StrictCheckAt 30 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 30) 30 30:=by decide +kernel
  have hfast:StrictAtFast (row 30 30) 30 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 30) 30 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 30) 30 30 hvalid hfast

theorem sr30p31:∀ i ∈ List.range 1,StrictCheckAt 30 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 31) 30 31:=by decide +kernel
  have hfast:StrictAtFast (row 30 31) 30 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 31) 30 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 31) 30 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
