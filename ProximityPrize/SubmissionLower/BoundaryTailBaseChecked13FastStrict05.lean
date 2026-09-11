import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr13p64:∀ i ∈ List.range 1,StrictCheckAt 13 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 64) 13 64:=by decide +kernel
  have hfast:StrictAtFast (row 13 64) 13 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 64) 13 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 64) 13 64 hvalid hfast

theorem sr13p65:∀ i ∈ List.range 1,StrictCheckAt 13 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 65) 13 65:=by decide +kernel
  have hfast:StrictAtFast (row 13 65) 13 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 65) 13 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 65) 13 65 hvalid hfast

theorem sr13p66:∀ i ∈ List.range 1,StrictCheckAt 13 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 66) 13 66:=by decide +kernel
  have hfast:StrictAtFast (row 13 66) 13 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 66) 13 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 66) 13 66 hvalid hfast

theorem sr13p67:∀ i ∈ List.range 1,StrictCheckAt 13 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 67) 13 67:=by decide +kernel
  have hfast:StrictAtFast (row 13 67) 13 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 67) 13 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 67) 13 67 hvalid hfast

theorem sr13p68:∀ i ∈ List.range 1,StrictCheckAt 13 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 68) 13 68:=by decide +kernel
  have hfast:StrictAtFast (row 13 68) 13 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 68) 13 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 68) 13 68 hvalid hfast

theorem sr13p69:∀ i ∈ List.range 1,StrictCheckAt 13 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 69) 13 69:=by decide +kernel
  have hfast:StrictAtFast (row 13 69) 13 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 69) 13 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 69) 13 69 hvalid hfast

theorem sr13p70:∀ i ∈ List.range 1,StrictCheckAt 13 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 70) 13 70:=by decide +kernel
  have hfast:StrictAtFast (row 13 70) 13 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 70) 13 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 70) 13 70 hvalid hfast

theorem sr13p71:∀ i ∈ List.range 1,StrictCheckAt 13 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 71) 13 71:=by decide +kernel
  have hfast:StrictAtFast (row 13 71) 13 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 71) 13 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 71) 13 71 hvalid hfast

theorem sr13p72:∀ i ∈ List.range 1,StrictCheckAt 13 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 72) 13 72:=by decide +kernel
  have hfast:StrictAtFast (row 13 72) 13 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 72) 13 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 72) 13 72 hvalid hfast

theorem sr13p73:∀ i ∈ List.range 1,StrictCheckAt 13 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 73) 13 73:=by decide +kernel
  have hfast:StrictAtFast (row 13 73) 13 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 73) 13 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 73) 13 73 hvalid hfast

theorem sr13p74:∀ i ∈ List.range 1,StrictCheckAt 13 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 74) 13 74:=by decide +kernel
  have hfast:StrictAtFast (row 13 74) 13 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 74) 13 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 74) 13 74 hvalid hfast

theorem sr13p75:∀ i ∈ List.range 1,StrictCheckAt 13 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 75) 13 75:=by decide +kernel
  have hfast:StrictAtFast (row 13 75) 13 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 75) 13 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 75) 13 75 hvalid hfast

theorem sr13p76:∀ i ∈ List.range 1,StrictCheckAt 13 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 76) 13 76:=by decide +kernel
  have hfast:StrictAtFast (row 13 76) 13 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 76) 13 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 76) 13 76 hvalid hfast

theorem sr13p77:∀ i ∈ List.range 1,StrictCheckAt 13 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 77) 13 77:=by decide +kernel
  have hfast:StrictAtFast (row 13 77) 13 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 77) 13 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 77) 13 77 hvalid hfast

theorem sr13p78:∀ i ∈ List.range 1,StrictCheckAt 13 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 78) 13 78:=by decide +kernel
  have hfast:StrictAtFast (row 13 78) 13 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 78) 13 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 78) 13 78 hvalid hfast

theorem sr13p79:∀ i ∈ List.range 1,StrictCheckAt 13 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 79) 13 79:=by decide +kernel
  have hfast:StrictAtFast (row 13 79) 13 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 79) 13 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 79) 13 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
