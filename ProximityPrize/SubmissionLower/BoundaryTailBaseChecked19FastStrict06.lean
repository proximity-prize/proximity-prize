import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr19p80:∀ i ∈ List.range 1,StrictCheckAt 19 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 80) 19 80:=by decide +kernel
  have hfast:StrictAtFast (row 19 80) 19 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 80) 19 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 80) 19 80 hvalid hfast

theorem sr19p81:∀ i ∈ List.range 1,StrictCheckAt 19 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 81) 19 81:=by decide +kernel
  have hfast:StrictAtFast (row 19 81) 19 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 81) 19 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 81) 19 81 hvalid hfast

theorem sr19p82:∀ i ∈ List.range 1,StrictCheckAt 19 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 82) 19 82:=by decide +kernel
  have hfast:StrictAtFast (row 19 82) 19 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 82) 19 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 82) 19 82 hvalid hfast

theorem sr19p83:∀ i ∈ List.range 1,StrictCheckAt 19 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 83) 19 83:=by decide +kernel
  have hfast:StrictAtFast (row 19 83) 19 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 83) 19 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 83) 19 83 hvalid hfast

theorem sr19p84:∀ i ∈ List.range 1,StrictCheckAt 19 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 84) 19 84:=by decide +kernel
  have hfast:StrictAtFast (row 19 84) 19 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 84) 19 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 84) 19 84 hvalid hfast

theorem sr19p85:∀ i ∈ List.range 1,StrictCheckAt 19 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 85) 19 85:=by decide +kernel
  have hfast:StrictAtFast (row 19 85) 19 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 85) 19 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 85) 19 85 hvalid hfast

theorem sr19p86:∀ i ∈ List.range 1,StrictCheckAt 19 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 86) 19 86:=by decide +kernel
  have hfast:StrictAtFast (row 19 86) 19 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 86) 19 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 86) 19 86 hvalid hfast

theorem sr19p87:∀ i ∈ List.range 1,StrictCheckAt 19 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 87) 19 87:=by decide +kernel
  have hfast:StrictAtFast (row 19 87) 19 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 87) 19 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 87) 19 87 hvalid hfast

theorem sr19p88:∀ i ∈ List.range 1,StrictCheckAt 19 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 88) 19 88:=by decide +kernel
  have hfast:StrictAtFast (row 19 88) 19 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 88) 19 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 88) 19 88 hvalid hfast

theorem sr19p89:∀ i ∈ List.range 1,StrictCheckAt 19 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 89) 19 89:=by decide +kernel
  have hfast:StrictAtFast (row 19 89) 19 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 89) 19 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 89) 19 89 hvalid hfast

theorem sr19p90:∀ i ∈ List.range 1,StrictCheckAt 19 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 90) 19 90:=by decide +kernel
  have hfast:StrictAtFast (row 19 90) 19 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 90) 19 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 90) 19 90 hvalid hfast

theorem sr19p91:∀ i ∈ List.range 1,StrictCheckAt 19 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 91) 19 91:=by decide +kernel
  have hfast:StrictAtFast (row 19 91) 19 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 91) 19 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 91) 19 91 hvalid hfast

theorem sr19p92:∀ i ∈ List.range 1,StrictCheckAt 19 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 92) 19 92:=by decide +kernel
  have hfast:StrictAtFast (row 19 92) 19 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 92) 19 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 92) 19 92 hvalid hfast

theorem sr19p93:∀ i ∈ List.range 1,StrictCheckAt 19 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 93) 19 93:=by decide +kernel
  have hfast:StrictAtFast (row 19 93) 19 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 93) 19 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 93) 19 93 hvalid hfast

theorem sr19p94:∀ i ∈ List.range 1,StrictCheckAt 19 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 94) 19 94:=by decide +kernel
  have hfast:StrictAtFast (row 19 94) 19 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 94) 19 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 94) 19 94 hvalid hfast

theorem sr19p95:∀ i ∈ List.range 1,StrictCheckAt 19 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 95) 19 95:=by decide +kernel
  have hfast:StrictAtFast (row 19 95) 19 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 95) 19 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 95) 19 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
