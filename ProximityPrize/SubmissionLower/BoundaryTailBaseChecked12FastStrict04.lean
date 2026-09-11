import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr12p48:∀ i ∈ List.range 1,StrictCheckAt 12 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 48) 12 48:=by decide +kernel
  have hfast:StrictAtFast (row 12 48) 12 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 48) 12 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 48) 12 48 hvalid hfast

theorem sr12p49:∀ i ∈ List.range 1,StrictCheckAt 12 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 49) 12 49:=by decide +kernel
  have hfast:StrictAtFast (row 12 49) 12 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 49) 12 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 49) 12 49 hvalid hfast

theorem sr12p50:∀ i ∈ List.range 1,StrictCheckAt 12 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 50) 12 50:=by decide +kernel
  have hfast:StrictAtFast (row 12 50) 12 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 50) 12 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 50) 12 50 hvalid hfast

theorem sr12p51:∀ i ∈ List.range 1,StrictCheckAt 12 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 51) 12 51:=by decide +kernel
  have hfast:StrictAtFast (row 12 51) 12 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 51) 12 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 51) 12 51 hvalid hfast

theorem sr12p52:∀ i ∈ List.range 1,StrictCheckAt 12 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 52) 12 52:=by decide +kernel
  have hfast:StrictAtFast (row 12 52) 12 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 52) 12 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 52) 12 52 hvalid hfast

theorem sr12p53:∀ i ∈ List.range 1,StrictCheckAt 12 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 53) 12 53:=by decide +kernel
  have hfast:StrictAtFast (row 12 53) 12 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 53) 12 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 53) 12 53 hvalid hfast

theorem sr12p54:∀ i ∈ List.range 1,StrictCheckAt 12 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 54) 12 54:=by decide +kernel
  have hfast:StrictAtFast (row 12 54) 12 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 54) 12 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 54) 12 54 hvalid hfast

theorem sr12p55:∀ i ∈ List.range 1,StrictCheckAt 12 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 55) 12 55:=by decide +kernel
  have hfast:StrictAtFast (row 12 55) 12 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 55) 12 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 55) 12 55 hvalid hfast

theorem sr12p56:∀ i ∈ List.range 1,StrictCheckAt 12 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 56) 12 56:=by decide +kernel
  have hfast:StrictAtFast (row 12 56) 12 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 56) 12 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 56) 12 56 hvalid hfast

theorem sr12p57:∀ i ∈ List.range 1,StrictCheckAt 12 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 57) 12 57:=by decide +kernel
  have hfast:StrictAtFast (row 12 57) 12 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 57) 12 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 57) 12 57 hvalid hfast

theorem sr12p58:∀ i ∈ List.range 1,StrictCheckAt 12 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 58) 12 58:=by decide +kernel
  have hfast:StrictAtFast (row 12 58) 12 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 58) 12 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 58) 12 58 hvalid hfast

theorem sr12p59:∀ i ∈ List.range 1,StrictCheckAt 12 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 59) 12 59:=by decide +kernel
  have hfast:StrictAtFast (row 12 59) 12 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 59) 12 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 59) 12 59 hvalid hfast

theorem sr12p60:∀ i ∈ List.range 1,StrictCheckAt 12 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 60) 12 60:=by decide +kernel
  have hfast:StrictAtFast (row 12 60) 12 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 60) 12 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 60) 12 60 hvalid hfast

theorem sr12p61:∀ i ∈ List.range 1,StrictCheckAt 12 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 61) 12 61:=by decide +kernel
  have hfast:StrictAtFast (row 12 61) 12 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 61) 12 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 61) 12 61 hvalid hfast

theorem sr12p62:∀ i ∈ List.range 1,StrictCheckAt 12 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 62) 12 62:=by decide +kernel
  have hfast:StrictAtFast (row 12 62) 12 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 62) 12 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 62) 12 62 hvalid hfast

theorem sr12p63:∀ i ∈ List.range 1,StrictCheckAt 12 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 63) 12 63:=by decide +kernel
  have hfast:StrictAtFast (row 12 63) 12 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 63) 12 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 63) 12 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
