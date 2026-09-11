import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr31p80:∀ i ∈ List.range 1,StrictCheckAt 31 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 80) 31 80:=by decide +kernel
  have hfast:StrictAtFast (row 31 80) 31 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 80) 31 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 80) 31 80 hvalid hfast

theorem sr31p81:∀ i ∈ List.range 1,StrictCheckAt 31 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 81) 31 81:=by decide +kernel
  have hfast:StrictAtFast (row 31 81) 31 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 81) 31 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 81) 31 81 hvalid hfast

theorem sr31p82:∀ i ∈ List.range 1,StrictCheckAt 31 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 82) 31 82:=by decide +kernel
  have hfast:StrictAtFast (row 31 82) 31 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 82) 31 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 82) 31 82 hvalid hfast

theorem sr31p83:∀ i ∈ List.range 1,StrictCheckAt 31 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 83) 31 83:=by decide +kernel
  have hfast:StrictAtFast (row 31 83) 31 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 83) 31 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 83) 31 83 hvalid hfast

theorem sr31p84:∀ i ∈ List.range 1,StrictCheckAt 31 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 84) 31 84:=by decide +kernel
  have hfast:StrictAtFast (row 31 84) 31 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 84) 31 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 84) 31 84 hvalid hfast

theorem sr31p85:∀ i ∈ List.range 1,StrictCheckAt 31 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 85) 31 85:=by decide +kernel
  have hfast:StrictAtFast (row 31 85) 31 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 85) 31 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 85) 31 85 hvalid hfast

theorem sr31p86:∀ i ∈ List.range 1,StrictCheckAt 31 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 86) 31 86:=by decide +kernel
  have hfast:StrictAtFast (row 31 86) 31 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 86) 31 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 86) 31 86 hvalid hfast

theorem sr31p87:∀ i ∈ List.range 1,StrictCheckAt 31 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 87) 31 87:=by decide +kernel
  have hfast:StrictAtFast (row 31 87) 31 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 87) 31 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 87) 31 87 hvalid hfast

theorem sr31p88:∀ i ∈ List.range 1,StrictCheckAt 31 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 88) 31 88:=by decide +kernel
  have hfast:StrictAtFast (row 31 88) 31 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 88) 31 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 88) 31 88 hvalid hfast

theorem sr31p89:∀ i ∈ List.range 1,StrictCheckAt 31 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 89) 31 89:=by decide +kernel
  have hfast:StrictAtFast (row 31 89) 31 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 89) 31 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 89) 31 89 hvalid hfast

theorem sr31p90:∀ i ∈ List.range 1,StrictCheckAt 31 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 90) 31 90:=by decide +kernel
  have hfast:StrictAtFast (row 31 90) 31 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 90) 31 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 90) 31 90 hvalid hfast

theorem sr31p91:∀ i ∈ List.range 1,StrictCheckAt 31 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 91) 31 91:=by decide +kernel
  have hfast:StrictAtFast (row 31 91) 31 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 91) 31 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 91) 31 91 hvalid hfast

theorem sr31p92:∀ i ∈ List.range 1,StrictCheckAt 31 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 92) 31 92:=by decide +kernel
  have hfast:StrictAtFast (row 31 92) 31 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 92) 31 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 92) 31 92 hvalid hfast

theorem sr31p93:∀ i ∈ List.range 1,StrictCheckAt 31 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 93) 31 93:=by decide +kernel
  have hfast:StrictAtFast (row 31 93) 31 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 93) 31 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 93) 31 93 hvalid hfast

theorem sr31p94:∀ i ∈ List.range 1,StrictCheckAt 31 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 94) 31 94:=by decide +kernel
  have hfast:StrictAtFast (row 31 94) 31 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 94) 31 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 94) 31 94 hvalid hfast

theorem sr31p95:∀ i ∈ List.range 1,StrictCheckAt 31 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 95) 31 95:=by decide +kernel
  have hfast:StrictAtFast (row 31 95) 31 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 95) 31 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 95) 31 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
