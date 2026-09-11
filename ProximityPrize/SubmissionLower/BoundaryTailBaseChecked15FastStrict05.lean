import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr15p64:∀ i ∈ List.range 1,StrictCheckAt 15 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 64) 15 64:=by decide +kernel
  have hfast:StrictAtFast (row 15 64) 15 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 64) 15 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 64) 15 64 hvalid hfast

theorem sr15p65:∀ i ∈ List.range 1,StrictCheckAt 15 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 65) 15 65:=by decide +kernel
  have hfast:StrictAtFast (row 15 65) 15 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 65) 15 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 65) 15 65 hvalid hfast

theorem sr15p66:∀ i ∈ List.range 1,StrictCheckAt 15 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 66) 15 66:=by decide +kernel
  have hfast:StrictAtFast (row 15 66) 15 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 66) 15 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 66) 15 66 hvalid hfast

theorem sr15p67:∀ i ∈ List.range 1,StrictCheckAt 15 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 67) 15 67:=by decide +kernel
  have hfast:StrictAtFast (row 15 67) 15 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 67) 15 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 67) 15 67 hvalid hfast

theorem sr15p68:∀ i ∈ List.range 1,StrictCheckAt 15 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 68) 15 68:=by decide +kernel
  have hfast:StrictAtFast (row 15 68) 15 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 68) 15 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 68) 15 68 hvalid hfast

theorem sr15p69:∀ i ∈ List.range 1,StrictCheckAt 15 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 69) 15 69:=by decide +kernel
  have hfast:StrictAtFast (row 15 69) 15 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 69) 15 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 69) 15 69 hvalid hfast

theorem sr15p70:∀ i ∈ List.range 1,StrictCheckAt 15 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 70) 15 70:=by decide +kernel
  have hfast:StrictAtFast (row 15 70) 15 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 70) 15 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 70) 15 70 hvalid hfast

theorem sr15p71:∀ i ∈ List.range 1,StrictCheckAt 15 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 71) 15 71:=by decide +kernel
  have hfast:StrictAtFast (row 15 71) 15 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 71) 15 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 71) 15 71 hvalid hfast

theorem sr15p72:∀ i ∈ List.range 1,StrictCheckAt 15 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 72) 15 72:=by decide +kernel
  have hfast:StrictAtFast (row 15 72) 15 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 72) 15 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 72) 15 72 hvalid hfast

theorem sr15p73:∀ i ∈ List.range 1,StrictCheckAt 15 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 73) 15 73:=by decide +kernel
  have hfast:StrictAtFast (row 15 73) 15 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 73) 15 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 73) 15 73 hvalid hfast

theorem sr15p74:∀ i ∈ List.range 1,StrictCheckAt 15 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 74) 15 74:=by decide +kernel
  have hfast:StrictAtFast (row 15 74) 15 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 74) 15 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 74) 15 74 hvalid hfast

theorem sr15p75:∀ i ∈ List.range 1,StrictCheckAt 15 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 75) 15 75:=by decide +kernel
  have hfast:StrictAtFast (row 15 75) 15 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 75) 15 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 75) 15 75 hvalid hfast

theorem sr15p76:∀ i ∈ List.range 1,StrictCheckAt 15 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 76) 15 76:=by decide +kernel
  have hfast:StrictAtFast (row 15 76) 15 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 76) 15 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 76) 15 76 hvalid hfast

theorem sr15p77:∀ i ∈ List.range 1,StrictCheckAt 15 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 77) 15 77:=by decide +kernel
  have hfast:StrictAtFast (row 15 77) 15 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 77) 15 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 77) 15 77 hvalid hfast

theorem sr15p78:∀ i ∈ List.range 1,StrictCheckAt 15 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 78) 15 78:=by decide +kernel
  have hfast:StrictAtFast (row 15 78) 15 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 78) 15 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 78) 15 78 hvalid hfast

theorem sr15p79:∀ i ∈ List.range 1,StrictCheckAt 15 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 79) 15 79:=by decide +kernel
  have hfast:StrictAtFast (row 15 79) 15 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 79) 15 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 79) 15 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
