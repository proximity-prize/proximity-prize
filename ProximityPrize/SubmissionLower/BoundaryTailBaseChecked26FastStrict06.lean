import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr26p80:∀ i ∈ List.range 1,StrictCheckAt 26 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 80) 26 80:=by decide +kernel
  have hfast:StrictAtFast (row 26 80) 26 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 80) 26 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 80) 26 80 hvalid hfast

theorem sr26p81:∀ i ∈ List.range 1,StrictCheckAt 26 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 81) 26 81:=by decide +kernel
  have hfast:StrictAtFast (row 26 81) 26 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 81) 26 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 81) 26 81 hvalid hfast

theorem sr26p82:∀ i ∈ List.range 1,StrictCheckAt 26 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 82) 26 82:=by decide +kernel
  have hfast:StrictAtFast (row 26 82) 26 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 82) 26 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 82) 26 82 hvalid hfast

theorem sr26p83:∀ i ∈ List.range 1,StrictCheckAt 26 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 83) 26 83:=by decide +kernel
  have hfast:StrictAtFast (row 26 83) 26 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 83) 26 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 83) 26 83 hvalid hfast

theorem sr26p84:∀ i ∈ List.range 1,StrictCheckAt 26 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 84) 26 84:=by decide +kernel
  have hfast:StrictAtFast (row 26 84) 26 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 84) 26 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 84) 26 84 hvalid hfast

theorem sr26p85:∀ i ∈ List.range 1,StrictCheckAt 26 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 85) 26 85:=by decide +kernel
  have hfast:StrictAtFast (row 26 85) 26 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 85) 26 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 85) 26 85 hvalid hfast

theorem sr26p86:∀ i ∈ List.range 1,StrictCheckAt 26 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 86) 26 86:=by decide +kernel
  have hfast:StrictAtFast (row 26 86) 26 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 86) 26 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 86) 26 86 hvalid hfast

theorem sr26p87:∀ i ∈ List.range 1,StrictCheckAt 26 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 87) 26 87:=by decide +kernel
  have hfast:StrictAtFast (row 26 87) 26 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 87) 26 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 87) 26 87 hvalid hfast

theorem sr26p88:∀ i ∈ List.range 1,StrictCheckAt 26 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 88) 26 88:=by decide +kernel
  have hfast:StrictAtFast (row 26 88) 26 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 88) 26 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 88) 26 88 hvalid hfast

theorem sr26p89:∀ i ∈ List.range 1,StrictCheckAt 26 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 89) 26 89:=by decide +kernel
  have hfast:StrictAtFast (row 26 89) 26 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 89) 26 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 89) 26 89 hvalid hfast

theorem sr26p90:∀ i ∈ List.range 1,StrictCheckAt 26 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 90) 26 90:=by decide +kernel
  have hfast:StrictAtFast (row 26 90) 26 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 90) 26 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 90) 26 90 hvalid hfast

theorem sr26p91:∀ i ∈ List.range 1,StrictCheckAt 26 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 91) 26 91:=by decide +kernel
  have hfast:StrictAtFast (row 26 91) 26 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 91) 26 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 91) 26 91 hvalid hfast

theorem sr26p92:∀ i ∈ List.range 1,StrictCheckAt 26 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 92) 26 92:=by decide +kernel
  have hfast:StrictAtFast (row 26 92) 26 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 92) 26 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 92) 26 92 hvalid hfast

theorem sr26p93:∀ i ∈ List.range 1,StrictCheckAt 26 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 93) 26 93:=by decide +kernel
  have hfast:StrictAtFast (row 26 93) 26 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 93) 26 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 93) 26 93 hvalid hfast

theorem sr26p94:∀ i ∈ List.range 1,StrictCheckAt 26 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 94) 26 94:=by decide +kernel
  have hfast:StrictAtFast (row 26 94) 26 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 94) 26 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 94) 26 94 hvalid hfast

theorem sr26p95:∀ i ∈ List.range 1,StrictCheckAt 26 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 95) 26 95:=by decide +kernel
  have hfast:StrictAtFast (row 26 95) 26 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 95) 26 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 95) 26 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
