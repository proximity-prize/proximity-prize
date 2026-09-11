import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr27p48:∀ i ∈ List.range 1,StrictCheckAt 27 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 48) 27 48:=by decide +kernel
  have hfast:StrictAtFast (row 27 48) 27 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 48) 27 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 48) 27 48 hvalid hfast

theorem sr27p49:∀ i ∈ List.range 1,StrictCheckAt 27 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 49) 27 49:=by decide +kernel
  have hfast:StrictAtFast (row 27 49) 27 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 49) 27 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 49) 27 49 hvalid hfast

theorem sr27p50:∀ i ∈ List.range 1,StrictCheckAt 27 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 50) 27 50:=by decide +kernel
  have hfast:StrictAtFast (row 27 50) 27 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 50) 27 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 50) 27 50 hvalid hfast

theorem sr27p51:∀ i ∈ List.range 1,StrictCheckAt 27 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 51) 27 51:=by decide +kernel
  have hfast:StrictAtFast (row 27 51) 27 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 51) 27 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 51) 27 51 hvalid hfast

theorem sr27p52:∀ i ∈ List.range 1,StrictCheckAt 27 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 52) 27 52:=by decide +kernel
  have hfast:StrictAtFast (row 27 52) 27 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 52) 27 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 52) 27 52 hvalid hfast

theorem sr27p53:∀ i ∈ List.range 1,StrictCheckAt 27 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 53) 27 53:=by decide +kernel
  have hfast:StrictAtFast (row 27 53) 27 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 53) 27 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 53) 27 53 hvalid hfast

theorem sr27p54:∀ i ∈ List.range 1,StrictCheckAt 27 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 54) 27 54:=by decide +kernel
  have hfast:StrictAtFast (row 27 54) 27 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 54) 27 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 54) 27 54 hvalid hfast

theorem sr27p55:∀ i ∈ List.range 1,StrictCheckAt 27 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 55) 27 55:=by decide +kernel
  have hfast:StrictAtFast (row 27 55) 27 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 55) 27 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 55) 27 55 hvalid hfast

theorem sr27p56:∀ i ∈ List.range 1,StrictCheckAt 27 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 56) 27 56:=by decide +kernel
  have hfast:StrictAtFast (row 27 56) 27 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 56) 27 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 56) 27 56 hvalid hfast

theorem sr27p57:∀ i ∈ List.range 1,StrictCheckAt 27 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 57) 27 57:=by decide +kernel
  have hfast:StrictAtFast (row 27 57) 27 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 57) 27 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 57) 27 57 hvalid hfast

theorem sr27p58:∀ i ∈ List.range 1,StrictCheckAt 27 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 58) 27 58:=by decide +kernel
  have hfast:StrictAtFast (row 27 58) 27 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 58) 27 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 58) 27 58 hvalid hfast

theorem sr27p59:∀ i ∈ List.range 1,StrictCheckAt 27 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 59) 27 59:=by decide +kernel
  have hfast:StrictAtFast (row 27 59) 27 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 59) 27 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 59) 27 59 hvalid hfast

theorem sr27p60:∀ i ∈ List.range 1,StrictCheckAt 27 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 60) 27 60:=by decide +kernel
  have hfast:StrictAtFast (row 27 60) 27 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 60) 27 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 60) 27 60 hvalid hfast

theorem sr27p61:∀ i ∈ List.range 1,StrictCheckAt 27 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 61) 27 61:=by decide +kernel
  have hfast:StrictAtFast (row 27 61) 27 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 61) 27 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 61) 27 61 hvalid hfast

theorem sr27p62:∀ i ∈ List.range 1,StrictCheckAt 27 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 62) 27 62:=by decide +kernel
  have hfast:StrictAtFast (row 27 62) 27 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 62) 27 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 62) 27 62 hvalid hfast

theorem sr27p63:∀ i ∈ List.range 1,StrictCheckAt 27 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 63) 27 63:=by decide +kernel
  have hfast:StrictAtFast (row 27 63) 27 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 63) 27 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 63) 27 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
