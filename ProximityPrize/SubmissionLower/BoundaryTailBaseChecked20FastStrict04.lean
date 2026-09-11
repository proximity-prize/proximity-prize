import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr20p48:∀ i ∈ List.range 1,StrictCheckAt 20 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 48) 20 48:=by decide +kernel
  have hfast:StrictAtFast (row 20 48) 20 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 48) 20 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 48) 20 48 hvalid hfast

theorem sr20p49:∀ i ∈ List.range 1,StrictCheckAt 20 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 49) 20 49:=by decide +kernel
  have hfast:StrictAtFast (row 20 49) 20 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 49) 20 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 49) 20 49 hvalid hfast

theorem sr20p50:∀ i ∈ List.range 1,StrictCheckAt 20 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 50) 20 50:=by decide +kernel
  have hfast:StrictAtFast (row 20 50) 20 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 50) 20 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 50) 20 50 hvalid hfast

theorem sr20p51:∀ i ∈ List.range 1,StrictCheckAt 20 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 51) 20 51:=by decide +kernel
  have hfast:StrictAtFast (row 20 51) 20 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 51) 20 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 51) 20 51 hvalid hfast

theorem sr20p52:∀ i ∈ List.range 1,StrictCheckAt 20 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 52) 20 52:=by decide +kernel
  have hfast:StrictAtFast (row 20 52) 20 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 52) 20 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 52) 20 52 hvalid hfast

theorem sr20p53:∀ i ∈ List.range 1,StrictCheckAt 20 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 53) 20 53:=by decide +kernel
  have hfast:StrictAtFast (row 20 53) 20 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 53) 20 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 53) 20 53 hvalid hfast

theorem sr20p54:∀ i ∈ List.range 1,StrictCheckAt 20 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 54) 20 54:=by decide +kernel
  have hfast:StrictAtFast (row 20 54) 20 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 54) 20 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 54) 20 54 hvalid hfast

theorem sr20p55:∀ i ∈ List.range 1,StrictCheckAt 20 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 55) 20 55:=by decide +kernel
  have hfast:StrictAtFast (row 20 55) 20 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 55) 20 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 55) 20 55 hvalid hfast

theorem sr20p56:∀ i ∈ List.range 1,StrictCheckAt 20 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 56) 20 56:=by decide +kernel
  have hfast:StrictAtFast (row 20 56) 20 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 56) 20 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 56) 20 56 hvalid hfast

theorem sr20p57:∀ i ∈ List.range 1,StrictCheckAt 20 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 57) 20 57:=by decide +kernel
  have hfast:StrictAtFast (row 20 57) 20 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 57) 20 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 57) 20 57 hvalid hfast

theorem sr20p58:∀ i ∈ List.range 1,StrictCheckAt 20 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 58) 20 58:=by decide +kernel
  have hfast:StrictAtFast (row 20 58) 20 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 58) 20 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 58) 20 58 hvalid hfast

theorem sr20p59:∀ i ∈ List.range 1,StrictCheckAt 20 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 59) 20 59:=by decide +kernel
  have hfast:StrictAtFast (row 20 59) 20 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 59) 20 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 59) 20 59 hvalid hfast

theorem sr20p60:∀ i ∈ List.range 1,StrictCheckAt 20 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 60) 20 60:=by decide +kernel
  have hfast:StrictAtFast (row 20 60) 20 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 60) 20 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 60) 20 60 hvalid hfast

theorem sr20p61:∀ i ∈ List.range 1,StrictCheckAt 20 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 61) 20 61:=by decide +kernel
  have hfast:StrictAtFast (row 20 61) 20 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 61) 20 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 61) 20 61 hvalid hfast

theorem sr20p62:∀ i ∈ List.range 1,StrictCheckAt 20 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 62) 20 62:=by decide +kernel
  have hfast:StrictAtFast (row 20 62) 20 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 62) 20 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 62) 20 62 hvalid hfast

theorem sr20p63:∀ i ∈ List.range 1,StrictCheckAt 20 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 63) 20 63:=by decide +kernel
  have hfast:StrictAtFast (row 20 63) 20 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 63) 20 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 63) 20 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
