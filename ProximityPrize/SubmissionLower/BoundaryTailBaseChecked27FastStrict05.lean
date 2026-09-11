import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr27p64:∀ i ∈ List.range 1,StrictCheckAt 27 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 64) 27 64:=by decide +kernel
  have hfast:StrictAtFast (row 27 64) 27 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 64) 27 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 64) 27 64 hvalid hfast

theorem sr27p65:∀ i ∈ List.range 1,StrictCheckAt 27 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 65) 27 65:=by decide +kernel
  have hfast:StrictAtFast (row 27 65) 27 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 65) 27 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 65) 27 65 hvalid hfast

theorem sr27p66:∀ i ∈ List.range 1,StrictCheckAt 27 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 66) 27 66:=by decide +kernel
  have hfast:StrictAtFast (row 27 66) 27 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 66) 27 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 66) 27 66 hvalid hfast

theorem sr27p67:∀ i ∈ List.range 1,StrictCheckAt 27 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 67) 27 67:=by decide +kernel
  have hfast:StrictAtFast (row 27 67) 27 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 67) 27 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 67) 27 67 hvalid hfast

theorem sr27p68:∀ i ∈ List.range 1,StrictCheckAt 27 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 68) 27 68:=by decide +kernel
  have hfast:StrictAtFast (row 27 68) 27 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 68) 27 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 68) 27 68 hvalid hfast

theorem sr27p69:∀ i ∈ List.range 1,StrictCheckAt 27 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 69) 27 69:=by decide +kernel
  have hfast:StrictAtFast (row 27 69) 27 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 69) 27 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 69) 27 69 hvalid hfast

theorem sr27p70:∀ i ∈ List.range 1,StrictCheckAt 27 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 70) 27 70:=by decide +kernel
  have hfast:StrictAtFast (row 27 70) 27 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 70) 27 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 70) 27 70 hvalid hfast

theorem sr27p71:∀ i ∈ List.range 1,StrictCheckAt 27 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 71) 27 71:=by decide +kernel
  have hfast:StrictAtFast (row 27 71) 27 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 71) 27 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 71) 27 71 hvalid hfast

theorem sr27p72:∀ i ∈ List.range 1,StrictCheckAt 27 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 72) 27 72:=by decide +kernel
  have hfast:StrictAtFast (row 27 72) 27 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 72) 27 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 72) 27 72 hvalid hfast

theorem sr27p73:∀ i ∈ List.range 1,StrictCheckAt 27 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 73) 27 73:=by decide +kernel
  have hfast:StrictAtFast (row 27 73) 27 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 73) 27 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 73) 27 73 hvalid hfast

theorem sr27p74:∀ i ∈ List.range 1,StrictCheckAt 27 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 74) 27 74:=by decide +kernel
  have hfast:StrictAtFast (row 27 74) 27 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 74) 27 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 74) 27 74 hvalid hfast

theorem sr27p75:∀ i ∈ List.range 1,StrictCheckAt 27 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 75) 27 75:=by decide +kernel
  have hfast:StrictAtFast (row 27 75) 27 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 75) 27 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 75) 27 75 hvalid hfast

theorem sr27p76:∀ i ∈ List.range 1,StrictCheckAt 27 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 76) 27 76:=by decide +kernel
  have hfast:StrictAtFast (row 27 76) 27 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 76) 27 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 76) 27 76 hvalid hfast

theorem sr27p77:∀ i ∈ List.range 1,StrictCheckAt 27 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 77) 27 77:=by decide +kernel
  have hfast:StrictAtFast (row 27 77) 27 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 77) 27 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 77) 27 77 hvalid hfast

theorem sr27p78:∀ i ∈ List.range 1,StrictCheckAt 27 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 78) 27 78:=by decide +kernel
  have hfast:StrictAtFast (row 27 78) 27 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 78) 27 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 78) 27 78 hvalid hfast

theorem sr27p79:∀ i ∈ List.range 1,StrictCheckAt 27 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 79) 27 79:=by decide +kernel
  have hfast:StrictAtFast (row 27 79) 27 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 79) 27 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 79) 27 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
