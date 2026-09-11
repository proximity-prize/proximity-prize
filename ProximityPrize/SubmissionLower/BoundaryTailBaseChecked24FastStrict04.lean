import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr24p48:∀ i ∈ List.range 1,StrictCheckAt 24 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 48) 24 48:=by decide +kernel
  have hfast:StrictAtFast (row 24 48) 24 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 48) 24 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 48) 24 48 hvalid hfast

theorem sr24p49:∀ i ∈ List.range 1,StrictCheckAt 24 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 49) 24 49:=by decide +kernel
  have hfast:StrictAtFast (row 24 49) 24 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 49) 24 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 49) 24 49 hvalid hfast

theorem sr24p50:∀ i ∈ List.range 1,StrictCheckAt 24 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 50) 24 50:=by decide +kernel
  have hfast:StrictAtFast (row 24 50) 24 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 50) 24 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 50) 24 50 hvalid hfast

theorem sr24p51:∀ i ∈ List.range 1,StrictCheckAt 24 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 51) 24 51:=by decide +kernel
  have hfast:StrictAtFast (row 24 51) 24 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 51) 24 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 51) 24 51 hvalid hfast

theorem sr24p52:∀ i ∈ List.range 1,StrictCheckAt 24 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 52) 24 52:=by decide +kernel
  have hfast:StrictAtFast (row 24 52) 24 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 52) 24 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 52) 24 52 hvalid hfast

theorem sr24p53:∀ i ∈ List.range 1,StrictCheckAt 24 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 53) 24 53:=by decide +kernel
  have hfast:StrictAtFast (row 24 53) 24 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 53) 24 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 53) 24 53 hvalid hfast

theorem sr24p54:∀ i ∈ List.range 1,StrictCheckAt 24 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 54) 24 54:=by decide +kernel
  have hfast:StrictAtFast (row 24 54) 24 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 54) 24 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 54) 24 54 hvalid hfast

theorem sr24p55:∀ i ∈ List.range 1,StrictCheckAt 24 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 55) 24 55:=by decide +kernel
  have hfast:StrictAtFast (row 24 55) 24 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 55) 24 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 55) 24 55 hvalid hfast

theorem sr24p56:∀ i ∈ List.range 1,StrictCheckAt 24 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 56) 24 56:=by decide +kernel
  have hfast:StrictAtFast (row 24 56) 24 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 56) 24 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 56) 24 56 hvalid hfast

theorem sr24p57:∀ i ∈ List.range 1,StrictCheckAt 24 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 57) 24 57:=by decide +kernel
  have hfast:StrictAtFast (row 24 57) 24 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 57) 24 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 57) 24 57 hvalid hfast

theorem sr24p58:∀ i ∈ List.range 1,StrictCheckAt 24 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 58) 24 58:=by decide +kernel
  have hfast:StrictAtFast (row 24 58) 24 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 58) 24 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 58) 24 58 hvalid hfast

theorem sr24p59:∀ i ∈ List.range 1,StrictCheckAt 24 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 59) 24 59:=by decide +kernel
  have hfast:StrictAtFast (row 24 59) 24 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 59) 24 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 59) 24 59 hvalid hfast

theorem sr24p60:∀ i ∈ List.range 1,StrictCheckAt 24 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 60) 24 60:=by decide +kernel
  have hfast:StrictAtFast (row 24 60) 24 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 60) 24 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 60) 24 60 hvalid hfast

theorem sr24p61:∀ i ∈ List.range 1,StrictCheckAt 24 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 61) 24 61:=by decide +kernel
  have hfast:StrictAtFast (row 24 61) 24 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 61) 24 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 61) 24 61 hvalid hfast

theorem sr24p62:∀ i ∈ List.range 1,StrictCheckAt 24 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 62) 24 62:=by decide +kernel
  have hfast:StrictAtFast (row 24 62) 24 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 62) 24 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 62) 24 62 hvalid hfast

theorem sr24p63:∀ i ∈ List.range 1,StrictCheckAt 24 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 63) 24 63:=by decide +kernel
  have hfast:StrictAtFast (row 24 63) 24 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 63) 24 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 63) 24 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
