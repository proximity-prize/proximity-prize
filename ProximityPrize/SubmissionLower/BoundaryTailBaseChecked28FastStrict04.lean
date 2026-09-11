import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr28p48:∀ i ∈ List.range 1,StrictCheckAt 28 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 48) 28 48:=by decide +kernel
  have hfast:StrictAtFast (row 28 48) 28 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 48) 28 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 48) 28 48 hvalid hfast

theorem sr28p49:∀ i ∈ List.range 1,StrictCheckAt 28 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 49) 28 49:=by decide +kernel
  have hfast:StrictAtFast (row 28 49) 28 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 49) 28 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 49) 28 49 hvalid hfast

theorem sr28p50:∀ i ∈ List.range 1,StrictCheckAt 28 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 50) 28 50:=by decide +kernel
  have hfast:StrictAtFast (row 28 50) 28 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 50) 28 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 50) 28 50 hvalid hfast

theorem sr28p51:∀ i ∈ List.range 1,StrictCheckAt 28 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 51) 28 51:=by decide +kernel
  have hfast:StrictAtFast (row 28 51) 28 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 51) 28 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 51) 28 51 hvalid hfast

theorem sr28p52:∀ i ∈ List.range 1,StrictCheckAt 28 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 52) 28 52:=by decide +kernel
  have hfast:StrictAtFast (row 28 52) 28 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 52) 28 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 52) 28 52 hvalid hfast

theorem sr28p53:∀ i ∈ List.range 1,StrictCheckAt 28 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 53) 28 53:=by decide +kernel
  have hfast:StrictAtFast (row 28 53) 28 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 53) 28 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 53) 28 53 hvalid hfast

theorem sr28p54:∀ i ∈ List.range 1,StrictCheckAt 28 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 54) 28 54:=by decide +kernel
  have hfast:StrictAtFast (row 28 54) 28 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 54) 28 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 54) 28 54 hvalid hfast

theorem sr28p55:∀ i ∈ List.range 1,StrictCheckAt 28 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 55) 28 55:=by decide +kernel
  have hfast:StrictAtFast (row 28 55) 28 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 55) 28 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 55) 28 55 hvalid hfast

theorem sr28p56:∀ i ∈ List.range 1,StrictCheckAt 28 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 56) 28 56:=by decide +kernel
  have hfast:StrictAtFast (row 28 56) 28 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 56) 28 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 56) 28 56 hvalid hfast

theorem sr28p57:∀ i ∈ List.range 1,StrictCheckAt 28 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 57) 28 57:=by decide +kernel
  have hfast:StrictAtFast (row 28 57) 28 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 57) 28 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 57) 28 57 hvalid hfast

theorem sr28p58:∀ i ∈ List.range 1,StrictCheckAt 28 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 58) 28 58:=by decide +kernel
  have hfast:StrictAtFast (row 28 58) 28 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 58) 28 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 58) 28 58 hvalid hfast

theorem sr28p59:∀ i ∈ List.range 1,StrictCheckAt 28 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 59) 28 59:=by decide +kernel
  have hfast:StrictAtFast (row 28 59) 28 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 59) 28 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 59) 28 59 hvalid hfast

theorem sr28p60:∀ i ∈ List.range 1,StrictCheckAt 28 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 60) 28 60:=by decide +kernel
  have hfast:StrictAtFast (row 28 60) 28 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 60) 28 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 60) 28 60 hvalid hfast

theorem sr28p61:∀ i ∈ List.range 1,StrictCheckAt 28 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 61) 28 61:=by decide +kernel
  have hfast:StrictAtFast (row 28 61) 28 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 61) 28 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 61) 28 61 hvalid hfast

theorem sr28p62:∀ i ∈ List.range 1,StrictCheckAt 28 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 62) 28 62:=by decide +kernel
  have hfast:StrictAtFast (row 28 62) 28 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 62) 28 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 62) 28 62 hvalid hfast

theorem sr28p63:∀ i ∈ List.range 1,StrictCheckAt 28 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 63) 28 63:=by decide +kernel
  have hfast:StrictAtFast (row 28 63) 28 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 63) 28 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 63) 28 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
