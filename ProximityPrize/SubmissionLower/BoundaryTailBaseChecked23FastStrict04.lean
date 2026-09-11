import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr23p48:∀ i ∈ List.range 1,StrictCheckAt 23 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 48) 23 48:=by decide +kernel
  have hfast:StrictAtFast (row 23 48) 23 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 48) 23 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 48) 23 48 hvalid hfast

theorem sr23p49:∀ i ∈ List.range 1,StrictCheckAt 23 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 49) 23 49:=by decide +kernel
  have hfast:StrictAtFast (row 23 49) 23 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 49) 23 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 49) 23 49 hvalid hfast

theorem sr23p50:∀ i ∈ List.range 1,StrictCheckAt 23 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 50) 23 50:=by decide +kernel
  have hfast:StrictAtFast (row 23 50) 23 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 50) 23 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 50) 23 50 hvalid hfast

theorem sr23p51:∀ i ∈ List.range 1,StrictCheckAt 23 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 51) 23 51:=by decide +kernel
  have hfast:StrictAtFast (row 23 51) 23 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 51) 23 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 51) 23 51 hvalid hfast

theorem sr23p52:∀ i ∈ List.range 1,StrictCheckAt 23 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 52) 23 52:=by decide +kernel
  have hfast:StrictAtFast (row 23 52) 23 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 52) 23 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 52) 23 52 hvalid hfast

theorem sr23p53:∀ i ∈ List.range 1,StrictCheckAt 23 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 53) 23 53:=by decide +kernel
  have hfast:StrictAtFast (row 23 53) 23 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 53) 23 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 53) 23 53 hvalid hfast

theorem sr23p54:∀ i ∈ List.range 1,StrictCheckAt 23 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 54) 23 54:=by decide +kernel
  have hfast:StrictAtFast (row 23 54) 23 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 54) 23 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 54) 23 54 hvalid hfast

theorem sr23p55:∀ i ∈ List.range 1,StrictCheckAt 23 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 55) 23 55:=by decide +kernel
  have hfast:StrictAtFast (row 23 55) 23 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 55) 23 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 55) 23 55 hvalid hfast

theorem sr23p56:∀ i ∈ List.range 1,StrictCheckAt 23 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 56) 23 56:=by decide +kernel
  have hfast:StrictAtFast (row 23 56) 23 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 56) 23 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 56) 23 56 hvalid hfast

theorem sr23p57:∀ i ∈ List.range 1,StrictCheckAt 23 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 57) 23 57:=by decide +kernel
  have hfast:StrictAtFast (row 23 57) 23 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 57) 23 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 57) 23 57 hvalid hfast

theorem sr23p58:∀ i ∈ List.range 1,StrictCheckAt 23 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 58) 23 58:=by decide +kernel
  have hfast:StrictAtFast (row 23 58) 23 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 58) 23 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 58) 23 58 hvalid hfast

theorem sr23p59:∀ i ∈ List.range 1,StrictCheckAt 23 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 59) 23 59:=by decide +kernel
  have hfast:StrictAtFast (row 23 59) 23 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 59) 23 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 59) 23 59 hvalid hfast

theorem sr23p60:∀ i ∈ List.range 1,StrictCheckAt 23 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 60) 23 60:=by decide +kernel
  have hfast:StrictAtFast (row 23 60) 23 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 60) 23 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 60) 23 60 hvalid hfast

theorem sr23p61:∀ i ∈ List.range 1,StrictCheckAt 23 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 61) 23 61:=by decide +kernel
  have hfast:StrictAtFast (row 23 61) 23 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 61) 23 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 61) 23 61 hvalid hfast

theorem sr23p62:∀ i ∈ List.range 1,StrictCheckAt 23 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 62) 23 62:=by decide +kernel
  have hfast:StrictAtFast (row 23 62) 23 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 62) 23 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 62) 23 62 hvalid hfast

theorem sr23p63:∀ i ∈ List.range 1,StrictCheckAt 23 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 63) 23 63:=by decide +kernel
  have hfast:StrictAtFast (row 23 63) 23 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 63) 23 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 63) 23 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
