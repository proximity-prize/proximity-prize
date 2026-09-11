import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr29p48:∀ i ∈ List.range 1,StrictCheckAt 29 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 48) 29 48:=by decide +kernel
  have hfast:StrictAtFast (row 29 48) 29 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 48) 29 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 48) 29 48 hvalid hfast

theorem sr29p49:∀ i ∈ List.range 1,StrictCheckAt 29 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 49) 29 49:=by decide +kernel
  have hfast:StrictAtFast (row 29 49) 29 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 49) 29 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 49) 29 49 hvalid hfast

theorem sr29p50:∀ i ∈ List.range 1,StrictCheckAt 29 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 50) 29 50:=by decide +kernel
  have hfast:StrictAtFast (row 29 50) 29 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 50) 29 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 50) 29 50 hvalid hfast

theorem sr29p51:∀ i ∈ List.range 1,StrictCheckAt 29 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 51) 29 51:=by decide +kernel
  have hfast:StrictAtFast (row 29 51) 29 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 51) 29 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 51) 29 51 hvalid hfast

theorem sr29p52:∀ i ∈ List.range 1,StrictCheckAt 29 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 52) 29 52:=by decide +kernel
  have hfast:StrictAtFast (row 29 52) 29 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 52) 29 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 52) 29 52 hvalid hfast

theorem sr29p53:∀ i ∈ List.range 1,StrictCheckAt 29 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 53) 29 53:=by decide +kernel
  have hfast:StrictAtFast (row 29 53) 29 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 53) 29 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 53) 29 53 hvalid hfast

theorem sr29p54:∀ i ∈ List.range 1,StrictCheckAt 29 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 54) 29 54:=by decide +kernel
  have hfast:StrictAtFast (row 29 54) 29 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 54) 29 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 54) 29 54 hvalid hfast

theorem sr29p55:∀ i ∈ List.range 1,StrictCheckAt 29 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 55) 29 55:=by decide +kernel
  have hfast:StrictAtFast (row 29 55) 29 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 55) 29 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 55) 29 55 hvalid hfast

theorem sr29p56:∀ i ∈ List.range 1,StrictCheckAt 29 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 56) 29 56:=by decide +kernel
  have hfast:StrictAtFast (row 29 56) 29 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 56) 29 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 56) 29 56 hvalid hfast

theorem sr29p57:∀ i ∈ List.range 1,StrictCheckAt 29 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 57) 29 57:=by decide +kernel
  have hfast:StrictAtFast (row 29 57) 29 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 57) 29 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 57) 29 57 hvalid hfast

theorem sr29p58:∀ i ∈ List.range 1,StrictCheckAt 29 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 58) 29 58:=by decide +kernel
  have hfast:StrictAtFast (row 29 58) 29 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 58) 29 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 58) 29 58 hvalid hfast

theorem sr29p59:∀ i ∈ List.range 1,StrictCheckAt 29 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 59) 29 59:=by decide +kernel
  have hfast:StrictAtFast (row 29 59) 29 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 59) 29 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 59) 29 59 hvalid hfast

theorem sr29p60:∀ i ∈ List.range 1,StrictCheckAt 29 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 60) 29 60:=by decide +kernel
  have hfast:StrictAtFast (row 29 60) 29 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 60) 29 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 60) 29 60 hvalid hfast

theorem sr29p61:∀ i ∈ List.range 1,StrictCheckAt 29 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 61) 29 61:=by decide +kernel
  have hfast:StrictAtFast (row 29 61) 29 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 61) 29 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 61) 29 61 hvalid hfast

theorem sr29p62:∀ i ∈ List.range 1,StrictCheckAt 29 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 62) 29 62:=by decide +kernel
  have hfast:StrictAtFast (row 29 62) 29 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 62) 29 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 62) 29 62 hvalid hfast

theorem sr29p63:∀ i ∈ List.range 1,StrictCheckAt 29 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 63) 29 63:=by decide +kernel
  have hfast:StrictAtFast (row 29 63) 29 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 63) 29 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 63) 29 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
