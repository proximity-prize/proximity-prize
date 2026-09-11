import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr15p48:∀ i ∈ List.range 1,StrictCheckAt 15 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 48) 15 48:=by decide +kernel
  have hfast:StrictAtFast (row 15 48) 15 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 48) 15 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 48) 15 48 hvalid hfast

theorem sr15p49:∀ i ∈ List.range 1,StrictCheckAt 15 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 49) 15 49:=by decide +kernel
  have hfast:StrictAtFast (row 15 49) 15 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 49) 15 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 49) 15 49 hvalid hfast

theorem sr15p50:∀ i ∈ List.range 1,StrictCheckAt 15 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 50) 15 50:=by decide +kernel
  have hfast:StrictAtFast (row 15 50) 15 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 50) 15 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 50) 15 50 hvalid hfast

theorem sr15p51:∀ i ∈ List.range 1,StrictCheckAt 15 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 51) 15 51:=by decide +kernel
  have hfast:StrictAtFast (row 15 51) 15 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 51) 15 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 51) 15 51 hvalid hfast

theorem sr15p52:∀ i ∈ List.range 1,StrictCheckAt 15 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 52) 15 52:=by decide +kernel
  have hfast:StrictAtFast (row 15 52) 15 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 52) 15 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 52) 15 52 hvalid hfast

theorem sr15p53:∀ i ∈ List.range 1,StrictCheckAt 15 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 53) 15 53:=by decide +kernel
  have hfast:StrictAtFast (row 15 53) 15 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 53) 15 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 53) 15 53 hvalid hfast

theorem sr15p54:∀ i ∈ List.range 1,StrictCheckAt 15 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 54) 15 54:=by decide +kernel
  have hfast:StrictAtFast (row 15 54) 15 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 54) 15 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 54) 15 54 hvalid hfast

theorem sr15p55:∀ i ∈ List.range 1,StrictCheckAt 15 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 55) 15 55:=by decide +kernel
  have hfast:StrictAtFast (row 15 55) 15 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 55) 15 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 55) 15 55 hvalid hfast

theorem sr15p56:∀ i ∈ List.range 1,StrictCheckAt 15 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 56) 15 56:=by decide +kernel
  have hfast:StrictAtFast (row 15 56) 15 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 56) 15 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 56) 15 56 hvalid hfast

theorem sr15p57:∀ i ∈ List.range 1,StrictCheckAt 15 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 57) 15 57:=by decide +kernel
  have hfast:StrictAtFast (row 15 57) 15 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 57) 15 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 57) 15 57 hvalid hfast

theorem sr15p58:∀ i ∈ List.range 1,StrictCheckAt 15 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 58) 15 58:=by decide +kernel
  have hfast:StrictAtFast (row 15 58) 15 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 58) 15 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 58) 15 58 hvalid hfast

theorem sr15p59:∀ i ∈ List.range 1,StrictCheckAt 15 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 59) 15 59:=by decide +kernel
  have hfast:StrictAtFast (row 15 59) 15 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 59) 15 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 59) 15 59 hvalid hfast

theorem sr15p60:∀ i ∈ List.range 1,StrictCheckAt 15 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 60) 15 60:=by decide +kernel
  have hfast:StrictAtFast (row 15 60) 15 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 60) 15 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 60) 15 60 hvalid hfast

theorem sr15p61:∀ i ∈ List.range 1,StrictCheckAt 15 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 61) 15 61:=by decide +kernel
  have hfast:StrictAtFast (row 15 61) 15 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 61) 15 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 61) 15 61 hvalid hfast

theorem sr15p62:∀ i ∈ List.range 1,StrictCheckAt 15 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 62) 15 62:=by decide +kernel
  have hfast:StrictAtFast (row 15 62) 15 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 62) 15 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 62) 15 62 hvalid hfast

theorem sr15p63:∀ i ∈ List.range 1,StrictCheckAt 15 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 63) 15 63:=by decide +kernel
  have hfast:StrictAtFast (row 15 63) 15 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 63) 15 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 63) 15 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
