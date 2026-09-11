import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr29p64:∀ i ∈ List.range 1,StrictCheckAt 29 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 64) 29 64:=by decide +kernel
  have hfast:StrictAtFast (row 29 64) 29 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 64) 29 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 64) 29 64 hvalid hfast

theorem sr29p65:∀ i ∈ List.range 1,StrictCheckAt 29 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 65) 29 65:=by decide +kernel
  have hfast:StrictAtFast (row 29 65) 29 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 65) 29 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 65) 29 65 hvalid hfast

theorem sr29p66:∀ i ∈ List.range 1,StrictCheckAt 29 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 66) 29 66:=by decide +kernel
  have hfast:StrictAtFast (row 29 66) 29 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 66) 29 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 66) 29 66 hvalid hfast

theorem sr29p67:∀ i ∈ List.range 1,StrictCheckAt 29 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 67) 29 67:=by decide +kernel
  have hfast:StrictAtFast (row 29 67) 29 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 67) 29 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 67) 29 67 hvalid hfast

theorem sr29p68:∀ i ∈ List.range 1,StrictCheckAt 29 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 68) 29 68:=by decide +kernel
  have hfast:StrictAtFast (row 29 68) 29 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 68) 29 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 68) 29 68 hvalid hfast

theorem sr29p69:∀ i ∈ List.range 1,StrictCheckAt 29 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 69) 29 69:=by decide +kernel
  have hfast:StrictAtFast (row 29 69) 29 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 69) 29 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 69) 29 69 hvalid hfast

theorem sr29p70:∀ i ∈ List.range 1,StrictCheckAt 29 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 70) 29 70:=by decide +kernel
  have hfast:StrictAtFast (row 29 70) 29 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 70) 29 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 70) 29 70 hvalid hfast

theorem sr29p71:∀ i ∈ List.range 1,StrictCheckAt 29 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 71) 29 71:=by decide +kernel
  have hfast:StrictAtFast (row 29 71) 29 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 71) 29 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 71) 29 71 hvalid hfast

theorem sr29p72:∀ i ∈ List.range 1,StrictCheckAt 29 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 72) 29 72:=by decide +kernel
  have hfast:StrictAtFast (row 29 72) 29 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 72) 29 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 72) 29 72 hvalid hfast

theorem sr29p73:∀ i ∈ List.range 1,StrictCheckAt 29 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 73) 29 73:=by decide +kernel
  have hfast:StrictAtFast (row 29 73) 29 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 73) 29 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 73) 29 73 hvalid hfast

theorem sr29p74:∀ i ∈ List.range 1,StrictCheckAt 29 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 74) 29 74:=by decide +kernel
  have hfast:StrictAtFast (row 29 74) 29 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 74) 29 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 74) 29 74 hvalid hfast

theorem sr29p75:∀ i ∈ List.range 1,StrictCheckAt 29 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 75) 29 75:=by decide +kernel
  have hfast:StrictAtFast (row 29 75) 29 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 75) 29 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 75) 29 75 hvalid hfast

theorem sr29p76:∀ i ∈ List.range 1,StrictCheckAt 29 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 76) 29 76:=by decide +kernel
  have hfast:StrictAtFast (row 29 76) 29 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 76) 29 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 76) 29 76 hvalid hfast

theorem sr29p77:∀ i ∈ List.range 1,StrictCheckAt 29 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 77) 29 77:=by decide +kernel
  have hfast:StrictAtFast (row 29 77) 29 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 77) 29 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 77) 29 77 hvalid hfast

theorem sr29p78:∀ i ∈ List.range 1,StrictCheckAt 29 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 78) 29 78:=by decide +kernel
  have hfast:StrictAtFast (row 29 78) 29 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 78) 29 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 78) 29 78 hvalid hfast

theorem sr29p79:∀ i ∈ List.range 1,StrictCheckAt 29 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 79) 29 79:=by decide +kernel
  have hfast:StrictAtFast (row 29 79) 29 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 79) 29 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 79) 29 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
