import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr25p64:∀ i ∈ List.range 1,StrictCheckAt 25 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 64) 25 64:=by decide +kernel
  have hfast:StrictAtFast (row 25 64) 25 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 64) 25 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 64) 25 64 hvalid hfast

theorem sr25p65:∀ i ∈ List.range 1,StrictCheckAt 25 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 65) 25 65:=by decide +kernel
  have hfast:StrictAtFast (row 25 65) 25 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 65) 25 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 65) 25 65 hvalid hfast

theorem sr25p66:∀ i ∈ List.range 1,StrictCheckAt 25 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 66) 25 66:=by decide +kernel
  have hfast:StrictAtFast (row 25 66) 25 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 66) 25 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 66) 25 66 hvalid hfast

theorem sr25p67:∀ i ∈ List.range 1,StrictCheckAt 25 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 67) 25 67:=by decide +kernel
  have hfast:StrictAtFast (row 25 67) 25 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 67) 25 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 67) 25 67 hvalid hfast

theorem sr25p68:∀ i ∈ List.range 1,StrictCheckAt 25 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 68) 25 68:=by decide +kernel
  have hfast:StrictAtFast (row 25 68) 25 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 68) 25 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 68) 25 68 hvalid hfast

theorem sr25p69:∀ i ∈ List.range 1,StrictCheckAt 25 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 69) 25 69:=by decide +kernel
  have hfast:StrictAtFast (row 25 69) 25 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 69) 25 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 69) 25 69 hvalid hfast

theorem sr25p70:∀ i ∈ List.range 1,StrictCheckAt 25 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 70) 25 70:=by decide +kernel
  have hfast:StrictAtFast (row 25 70) 25 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 70) 25 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 70) 25 70 hvalid hfast

theorem sr25p71:∀ i ∈ List.range 1,StrictCheckAt 25 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 71) 25 71:=by decide +kernel
  have hfast:StrictAtFast (row 25 71) 25 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 71) 25 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 71) 25 71 hvalid hfast

theorem sr25p72:∀ i ∈ List.range 1,StrictCheckAt 25 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 72) 25 72:=by decide +kernel
  have hfast:StrictAtFast (row 25 72) 25 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 72) 25 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 72) 25 72 hvalid hfast

theorem sr25p73:∀ i ∈ List.range 1,StrictCheckAt 25 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 73) 25 73:=by decide +kernel
  have hfast:StrictAtFast (row 25 73) 25 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 73) 25 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 73) 25 73 hvalid hfast

theorem sr25p74:∀ i ∈ List.range 1,StrictCheckAt 25 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 74) 25 74:=by decide +kernel
  have hfast:StrictAtFast (row 25 74) 25 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 74) 25 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 74) 25 74 hvalid hfast

theorem sr25p75:∀ i ∈ List.range 1,StrictCheckAt 25 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 75) 25 75:=by decide +kernel
  have hfast:StrictAtFast (row 25 75) 25 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 75) 25 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 75) 25 75 hvalid hfast

theorem sr25p76:∀ i ∈ List.range 1,StrictCheckAt 25 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 76) 25 76:=by decide +kernel
  have hfast:StrictAtFast (row 25 76) 25 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 76) 25 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 76) 25 76 hvalid hfast

theorem sr25p77:∀ i ∈ List.range 1,StrictCheckAt 25 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 77) 25 77:=by decide +kernel
  have hfast:StrictAtFast (row 25 77) 25 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 77) 25 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 77) 25 77 hvalid hfast

theorem sr25p78:∀ i ∈ List.range 1,StrictCheckAt 25 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 78) 25 78:=by decide +kernel
  have hfast:StrictAtFast (row 25 78) 25 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 78) 25 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 78) 25 78 hvalid hfast

theorem sr25p79:∀ i ∈ List.range 1,StrictCheckAt 25 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 79) 25 79:=by decide +kernel
  have hfast:StrictAtFast (row 25 79) 25 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 79) 25 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 79) 25 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
