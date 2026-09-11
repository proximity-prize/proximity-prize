import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr15p80:∀ i ∈ List.range 1,StrictCheckAt 15 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 80) 15 80:=by decide +kernel
  have hfast:StrictAtFast (row 15 80) 15 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 80) 15 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 80) 15 80 hvalid hfast

theorem sr15p81:∀ i ∈ List.range 1,StrictCheckAt 15 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 81) 15 81:=by decide +kernel
  have hfast:StrictAtFast (row 15 81) 15 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 81) 15 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 81) 15 81 hvalid hfast

theorem sr15p82:∀ i ∈ List.range 1,StrictCheckAt 15 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 82) 15 82:=by decide +kernel
  have hfast:StrictAtFast (row 15 82) 15 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 82) 15 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 82) 15 82 hvalid hfast

theorem sr15p83:∀ i ∈ List.range 1,StrictCheckAt 15 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 83) 15 83:=by decide +kernel
  have hfast:StrictAtFast (row 15 83) 15 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 83) 15 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 83) 15 83 hvalid hfast

theorem sr15p84:∀ i ∈ List.range 1,StrictCheckAt 15 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 84) 15 84:=by decide +kernel
  have hfast:StrictAtFast (row 15 84) 15 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 84) 15 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 84) 15 84 hvalid hfast

theorem sr15p85:∀ i ∈ List.range 1,StrictCheckAt 15 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 85) 15 85:=by decide +kernel
  have hfast:StrictAtFast (row 15 85) 15 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 85) 15 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 85) 15 85 hvalid hfast

theorem sr15p86:∀ i ∈ List.range 1,StrictCheckAt 15 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 86) 15 86:=by decide +kernel
  have hfast:StrictAtFast (row 15 86) 15 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 86) 15 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 86) 15 86 hvalid hfast

theorem sr15p87:∀ i ∈ List.range 1,StrictCheckAt 15 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 87) 15 87:=by decide +kernel
  have hfast:StrictAtFast (row 15 87) 15 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 87) 15 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 87) 15 87 hvalid hfast

theorem sr15p88:∀ i ∈ List.range 1,StrictCheckAt 15 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 88) 15 88:=by decide +kernel
  have hfast:StrictAtFast (row 15 88) 15 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 88) 15 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 88) 15 88 hvalid hfast

theorem sr15p89:∀ i ∈ List.range 1,StrictCheckAt 15 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 89) 15 89:=by decide +kernel
  have hfast:StrictAtFast (row 15 89) 15 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 89) 15 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 89) 15 89 hvalid hfast

theorem sr15p90:∀ i ∈ List.range 1,StrictCheckAt 15 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 90) 15 90:=by decide +kernel
  have hfast:StrictAtFast (row 15 90) 15 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 90) 15 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 90) 15 90 hvalid hfast

theorem sr15p91:∀ i ∈ List.range 1,StrictCheckAt 15 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 91) 15 91:=by decide +kernel
  have hfast:StrictAtFast (row 15 91) 15 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 91) 15 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 91) 15 91 hvalid hfast

theorem sr15p92:∀ i ∈ List.range 1,StrictCheckAt 15 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 92) 15 92:=by decide +kernel
  have hfast:StrictAtFast (row 15 92) 15 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 92) 15 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 92) 15 92 hvalid hfast

theorem sr15p93:∀ i ∈ List.range 1,StrictCheckAt 15 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 93) 15 93:=by decide +kernel
  have hfast:StrictAtFast (row 15 93) 15 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 93) 15 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 93) 15 93 hvalid hfast

theorem sr15p94:∀ i ∈ List.range 1,StrictCheckAt 15 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 94) 15 94:=by decide +kernel
  have hfast:StrictAtFast (row 15 94) 15 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 94) 15 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 94) 15 94 hvalid hfast

theorem sr15p95:∀ i ∈ List.range 1,StrictCheckAt 15 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 95) 15 95:=by decide +kernel
  have hfast:StrictAtFast (row 15 95) 15 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 95) 15 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 95) 15 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
