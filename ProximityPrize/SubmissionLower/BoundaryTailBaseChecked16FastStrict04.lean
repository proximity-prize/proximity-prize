import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr16p48:∀ i ∈ List.range 1,StrictCheckAt 16 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 48) 16 48:=by decide +kernel
  have hfast:StrictAtFast (row 16 48) 16 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 48) 16 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 48) 16 48 hvalid hfast

theorem sr16p49:∀ i ∈ List.range 1,StrictCheckAt 16 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 49) 16 49:=by decide +kernel
  have hfast:StrictAtFast (row 16 49) 16 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 49) 16 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 49) 16 49 hvalid hfast

theorem sr16p50:∀ i ∈ List.range 1,StrictCheckAt 16 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 50) 16 50:=by decide +kernel
  have hfast:StrictAtFast (row 16 50) 16 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 50) 16 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 50) 16 50 hvalid hfast

theorem sr16p51:∀ i ∈ List.range 1,StrictCheckAt 16 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 51) 16 51:=by decide +kernel
  have hfast:StrictAtFast (row 16 51) 16 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 51) 16 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 51) 16 51 hvalid hfast

theorem sr16p52:∀ i ∈ List.range 1,StrictCheckAt 16 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 52) 16 52:=by decide +kernel
  have hfast:StrictAtFast (row 16 52) 16 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 52) 16 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 52) 16 52 hvalid hfast

theorem sr16p53:∀ i ∈ List.range 1,StrictCheckAt 16 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 53) 16 53:=by decide +kernel
  have hfast:StrictAtFast (row 16 53) 16 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 53) 16 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 53) 16 53 hvalid hfast

theorem sr16p54:∀ i ∈ List.range 1,StrictCheckAt 16 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 54) 16 54:=by decide +kernel
  have hfast:StrictAtFast (row 16 54) 16 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 54) 16 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 54) 16 54 hvalid hfast

theorem sr16p55:∀ i ∈ List.range 1,StrictCheckAt 16 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 55) 16 55:=by decide +kernel
  have hfast:StrictAtFast (row 16 55) 16 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 55) 16 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 55) 16 55 hvalid hfast

theorem sr16p56:∀ i ∈ List.range 1,StrictCheckAt 16 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 56) 16 56:=by decide +kernel
  have hfast:StrictAtFast (row 16 56) 16 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 56) 16 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 56) 16 56 hvalid hfast

theorem sr16p57:∀ i ∈ List.range 1,StrictCheckAt 16 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 57) 16 57:=by decide +kernel
  have hfast:StrictAtFast (row 16 57) 16 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 57) 16 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 57) 16 57 hvalid hfast

theorem sr16p58:∀ i ∈ List.range 1,StrictCheckAt 16 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 58) 16 58:=by decide +kernel
  have hfast:StrictAtFast (row 16 58) 16 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 58) 16 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 58) 16 58 hvalid hfast

theorem sr16p59:∀ i ∈ List.range 1,StrictCheckAt 16 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 59) 16 59:=by decide +kernel
  have hfast:StrictAtFast (row 16 59) 16 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 59) 16 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 59) 16 59 hvalid hfast

theorem sr16p60:∀ i ∈ List.range 1,StrictCheckAt 16 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 60) 16 60:=by decide +kernel
  have hfast:StrictAtFast (row 16 60) 16 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 60) 16 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 60) 16 60 hvalid hfast

theorem sr16p61:∀ i ∈ List.range 1,StrictCheckAt 16 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 61) 16 61:=by decide +kernel
  have hfast:StrictAtFast (row 16 61) 16 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 61) 16 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 61) 16 61 hvalid hfast

theorem sr16p62:∀ i ∈ List.range 1,StrictCheckAt 16 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 62) 16 62:=by decide +kernel
  have hfast:StrictAtFast (row 16 62) 16 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 62) 16 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 62) 16 62 hvalid hfast

theorem sr16p63:∀ i ∈ List.range 1,StrictCheckAt 16 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 63) 16 63:=by decide +kernel
  have hfast:StrictAtFast (row 16 63) 16 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 63) 16 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 63) 16 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
