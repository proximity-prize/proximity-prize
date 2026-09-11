import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr16p80:∀ i ∈ List.range 1,StrictCheckAt 16 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 80) 16 80:=by decide +kernel
  have hfast:StrictAtFast (row 16 80) 16 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 80) 16 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 80) 16 80 hvalid hfast

theorem sr16p81:∀ i ∈ List.range 1,StrictCheckAt 16 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 81) 16 81:=by decide +kernel
  have hfast:StrictAtFast (row 16 81) 16 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 81) 16 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 81) 16 81 hvalid hfast

theorem sr16p82:∀ i ∈ List.range 1,StrictCheckAt 16 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 82) 16 82:=by decide +kernel
  have hfast:StrictAtFast (row 16 82) 16 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 82) 16 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 82) 16 82 hvalid hfast

theorem sr16p83:∀ i ∈ List.range 1,StrictCheckAt 16 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 83) 16 83:=by decide +kernel
  have hfast:StrictAtFast (row 16 83) 16 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 83) 16 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 83) 16 83 hvalid hfast

theorem sr16p84:∀ i ∈ List.range 1,StrictCheckAt 16 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 84) 16 84:=by decide +kernel
  have hfast:StrictAtFast (row 16 84) 16 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 84) 16 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 84) 16 84 hvalid hfast

theorem sr16p85:∀ i ∈ List.range 1,StrictCheckAt 16 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 85) 16 85:=by decide +kernel
  have hfast:StrictAtFast (row 16 85) 16 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 85) 16 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 85) 16 85 hvalid hfast

theorem sr16p86:∀ i ∈ List.range 1,StrictCheckAt 16 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 86) 16 86:=by decide +kernel
  have hfast:StrictAtFast (row 16 86) 16 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 86) 16 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 86) 16 86 hvalid hfast

theorem sr16p87:∀ i ∈ List.range 1,StrictCheckAt 16 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 87) 16 87:=by decide +kernel
  have hfast:StrictAtFast (row 16 87) 16 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 87) 16 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 87) 16 87 hvalid hfast

theorem sr16p88:∀ i ∈ List.range 1,StrictCheckAt 16 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 88) 16 88:=by decide +kernel
  have hfast:StrictAtFast (row 16 88) 16 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 88) 16 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 88) 16 88 hvalid hfast

theorem sr16p89:∀ i ∈ List.range 1,StrictCheckAt 16 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 89) 16 89:=by decide +kernel
  have hfast:StrictAtFast (row 16 89) 16 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 89) 16 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 89) 16 89 hvalid hfast

theorem sr16p90:∀ i ∈ List.range 1,StrictCheckAt 16 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 90) 16 90:=by decide +kernel
  have hfast:StrictAtFast (row 16 90) 16 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 90) 16 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 90) 16 90 hvalid hfast

theorem sr16p91:∀ i ∈ List.range 1,StrictCheckAt 16 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 91) 16 91:=by decide +kernel
  have hfast:StrictAtFast (row 16 91) 16 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 91) 16 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 91) 16 91 hvalid hfast

theorem sr16p92:∀ i ∈ List.range 1,StrictCheckAt 16 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 92) 16 92:=by decide +kernel
  have hfast:StrictAtFast (row 16 92) 16 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 92) 16 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 92) 16 92 hvalid hfast

theorem sr16p93:∀ i ∈ List.range 1,StrictCheckAt 16 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 93) 16 93:=by decide +kernel
  have hfast:StrictAtFast (row 16 93) 16 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 93) 16 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 93) 16 93 hvalid hfast

theorem sr16p94:∀ i ∈ List.range 1,StrictCheckAt 16 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 94) 16 94:=by decide +kernel
  have hfast:StrictAtFast (row 16 94) 16 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 94) 16 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 94) 16 94 hvalid hfast

theorem sr16p95:∀ i ∈ List.range 1,StrictCheckAt 16 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 95) 16 95:=by decide +kernel
  have hfast:StrictAtFast (row 16 95) 16 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 95) 16 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 95) 16 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
