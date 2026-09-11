import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr19p48:∀ i ∈ List.range 1,StrictCheckAt 19 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 48) 19 48:=by decide +kernel
  have hfast:StrictAtFast (row 19 48) 19 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 48) 19 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 48) 19 48 hvalid hfast

theorem sr19p49:∀ i ∈ List.range 1,StrictCheckAt 19 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 49) 19 49:=by decide +kernel
  have hfast:StrictAtFast (row 19 49) 19 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 49) 19 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 49) 19 49 hvalid hfast

theorem sr19p50:∀ i ∈ List.range 1,StrictCheckAt 19 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 50) 19 50:=by decide +kernel
  have hfast:StrictAtFast (row 19 50) 19 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 50) 19 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 50) 19 50 hvalid hfast

theorem sr19p51:∀ i ∈ List.range 1,StrictCheckAt 19 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 51) 19 51:=by decide +kernel
  have hfast:StrictAtFast (row 19 51) 19 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 51) 19 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 51) 19 51 hvalid hfast

theorem sr19p52:∀ i ∈ List.range 1,StrictCheckAt 19 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 52) 19 52:=by decide +kernel
  have hfast:StrictAtFast (row 19 52) 19 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 52) 19 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 52) 19 52 hvalid hfast

theorem sr19p53:∀ i ∈ List.range 1,StrictCheckAt 19 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 53) 19 53:=by decide +kernel
  have hfast:StrictAtFast (row 19 53) 19 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 53) 19 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 53) 19 53 hvalid hfast

theorem sr19p54:∀ i ∈ List.range 1,StrictCheckAt 19 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 54) 19 54:=by decide +kernel
  have hfast:StrictAtFast (row 19 54) 19 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 54) 19 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 54) 19 54 hvalid hfast

theorem sr19p55:∀ i ∈ List.range 1,StrictCheckAt 19 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 55) 19 55:=by decide +kernel
  have hfast:StrictAtFast (row 19 55) 19 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 55) 19 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 55) 19 55 hvalid hfast

theorem sr19p56:∀ i ∈ List.range 1,StrictCheckAt 19 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 56) 19 56:=by decide +kernel
  have hfast:StrictAtFast (row 19 56) 19 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 56) 19 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 56) 19 56 hvalid hfast

theorem sr19p57:∀ i ∈ List.range 1,StrictCheckAt 19 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 57) 19 57:=by decide +kernel
  have hfast:StrictAtFast (row 19 57) 19 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 57) 19 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 57) 19 57 hvalid hfast

theorem sr19p58:∀ i ∈ List.range 1,StrictCheckAt 19 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 58) 19 58:=by decide +kernel
  have hfast:StrictAtFast (row 19 58) 19 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 58) 19 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 58) 19 58 hvalid hfast

theorem sr19p59:∀ i ∈ List.range 1,StrictCheckAt 19 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 59) 19 59:=by decide +kernel
  have hfast:StrictAtFast (row 19 59) 19 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 59) 19 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 59) 19 59 hvalid hfast

theorem sr19p60:∀ i ∈ List.range 1,StrictCheckAt 19 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 60) 19 60:=by decide +kernel
  have hfast:StrictAtFast (row 19 60) 19 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 60) 19 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 60) 19 60 hvalid hfast

theorem sr19p61:∀ i ∈ List.range 1,StrictCheckAt 19 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 61) 19 61:=by decide +kernel
  have hfast:StrictAtFast (row 19 61) 19 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 61) 19 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 61) 19 61 hvalid hfast

theorem sr19p62:∀ i ∈ List.range 1,StrictCheckAt 19 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 62) 19 62:=by decide +kernel
  have hfast:StrictAtFast (row 19 62) 19 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 62) 19 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 62) 19 62 hvalid hfast

theorem sr19p63:∀ i ∈ List.range 1,StrictCheckAt 19 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 63) 19 63:=by decide +kernel
  have hfast:StrictAtFast (row 19 63) 19 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 63) 19 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 63) 19 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
