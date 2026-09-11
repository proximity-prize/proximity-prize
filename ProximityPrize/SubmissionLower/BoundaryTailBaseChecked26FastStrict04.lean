import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr26p48:∀ i ∈ List.range 1,StrictCheckAt 26 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 48) 26 48:=by decide +kernel
  have hfast:StrictAtFast (row 26 48) 26 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 48) 26 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 48) 26 48 hvalid hfast

theorem sr26p49:∀ i ∈ List.range 1,StrictCheckAt 26 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 49) 26 49:=by decide +kernel
  have hfast:StrictAtFast (row 26 49) 26 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 49) 26 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 49) 26 49 hvalid hfast

theorem sr26p50:∀ i ∈ List.range 1,StrictCheckAt 26 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 50) 26 50:=by decide +kernel
  have hfast:StrictAtFast (row 26 50) 26 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 50) 26 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 50) 26 50 hvalid hfast

theorem sr26p51:∀ i ∈ List.range 1,StrictCheckAt 26 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 51) 26 51:=by decide +kernel
  have hfast:StrictAtFast (row 26 51) 26 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 51) 26 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 51) 26 51 hvalid hfast

theorem sr26p52:∀ i ∈ List.range 1,StrictCheckAt 26 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 52) 26 52:=by decide +kernel
  have hfast:StrictAtFast (row 26 52) 26 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 52) 26 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 52) 26 52 hvalid hfast

theorem sr26p53:∀ i ∈ List.range 1,StrictCheckAt 26 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 53) 26 53:=by decide +kernel
  have hfast:StrictAtFast (row 26 53) 26 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 53) 26 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 53) 26 53 hvalid hfast

theorem sr26p54:∀ i ∈ List.range 1,StrictCheckAt 26 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 54) 26 54:=by decide +kernel
  have hfast:StrictAtFast (row 26 54) 26 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 54) 26 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 54) 26 54 hvalid hfast

theorem sr26p55:∀ i ∈ List.range 1,StrictCheckAt 26 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 55) 26 55:=by decide +kernel
  have hfast:StrictAtFast (row 26 55) 26 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 55) 26 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 55) 26 55 hvalid hfast

theorem sr26p56:∀ i ∈ List.range 1,StrictCheckAt 26 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 56) 26 56:=by decide +kernel
  have hfast:StrictAtFast (row 26 56) 26 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 56) 26 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 56) 26 56 hvalid hfast

theorem sr26p57:∀ i ∈ List.range 1,StrictCheckAt 26 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 57) 26 57:=by decide +kernel
  have hfast:StrictAtFast (row 26 57) 26 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 57) 26 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 57) 26 57 hvalid hfast

theorem sr26p58:∀ i ∈ List.range 1,StrictCheckAt 26 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 58) 26 58:=by decide +kernel
  have hfast:StrictAtFast (row 26 58) 26 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 58) 26 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 58) 26 58 hvalid hfast

theorem sr26p59:∀ i ∈ List.range 1,StrictCheckAt 26 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 59) 26 59:=by decide +kernel
  have hfast:StrictAtFast (row 26 59) 26 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 59) 26 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 59) 26 59 hvalid hfast

theorem sr26p60:∀ i ∈ List.range 1,StrictCheckAt 26 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 60) 26 60:=by decide +kernel
  have hfast:StrictAtFast (row 26 60) 26 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 60) 26 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 60) 26 60 hvalid hfast

theorem sr26p61:∀ i ∈ List.range 1,StrictCheckAt 26 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 61) 26 61:=by decide +kernel
  have hfast:StrictAtFast (row 26 61) 26 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 61) 26 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 61) 26 61 hvalid hfast

theorem sr26p62:∀ i ∈ List.range 1,StrictCheckAt 26 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 62) 26 62:=by decide +kernel
  have hfast:StrictAtFast (row 26 62) 26 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 62) 26 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 62) 26 62 hvalid hfast

theorem sr26p63:∀ i ∈ List.range 1,StrictCheckAt 26 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 63) 26 63:=by decide +kernel
  have hfast:StrictAtFast (row 26 63) 26 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 63) 26 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 63) 26 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
