import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr28p64:∀ i ∈ List.range 1,StrictCheckAt 28 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 64) 28 64:=by decide +kernel
  have hfast:StrictAtFast (row 28 64) 28 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 64) 28 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 64) 28 64 hvalid hfast

theorem sr28p65:∀ i ∈ List.range 1,StrictCheckAt 28 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 65) 28 65:=by decide +kernel
  have hfast:StrictAtFast (row 28 65) 28 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 65) 28 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 65) 28 65 hvalid hfast

theorem sr28p66:∀ i ∈ List.range 1,StrictCheckAt 28 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 66) 28 66:=by decide +kernel
  have hfast:StrictAtFast (row 28 66) 28 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 66) 28 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 66) 28 66 hvalid hfast

theorem sr28p67:∀ i ∈ List.range 1,StrictCheckAt 28 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 67) 28 67:=by decide +kernel
  have hfast:StrictAtFast (row 28 67) 28 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 67) 28 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 67) 28 67 hvalid hfast

theorem sr28p68:∀ i ∈ List.range 1,StrictCheckAt 28 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 68) 28 68:=by decide +kernel
  have hfast:StrictAtFast (row 28 68) 28 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 68) 28 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 68) 28 68 hvalid hfast

theorem sr28p69:∀ i ∈ List.range 1,StrictCheckAt 28 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 69) 28 69:=by decide +kernel
  have hfast:StrictAtFast (row 28 69) 28 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 69) 28 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 69) 28 69 hvalid hfast

theorem sr28p70:∀ i ∈ List.range 1,StrictCheckAt 28 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 70) 28 70:=by decide +kernel
  have hfast:StrictAtFast (row 28 70) 28 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 70) 28 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 70) 28 70 hvalid hfast

theorem sr28p71:∀ i ∈ List.range 1,StrictCheckAt 28 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 71) 28 71:=by decide +kernel
  have hfast:StrictAtFast (row 28 71) 28 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 71) 28 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 71) 28 71 hvalid hfast

theorem sr28p72:∀ i ∈ List.range 1,StrictCheckAt 28 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 72) 28 72:=by decide +kernel
  have hfast:StrictAtFast (row 28 72) 28 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 72) 28 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 72) 28 72 hvalid hfast

theorem sr28p73:∀ i ∈ List.range 1,StrictCheckAt 28 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 73) 28 73:=by decide +kernel
  have hfast:StrictAtFast (row 28 73) 28 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 73) 28 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 73) 28 73 hvalid hfast

theorem sr28p74:∀ i ∈ List.range 1,StrictCheckAt 28 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 74) 28 74:=by decide +kernel
  have hfast:StrictAtFast (row 28 74) 28 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 74) 28 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 74) 28 74 hvalid hfast

theorem sr28p75:∀ i ∈ List.range 1,StrictCheckAt 28 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 75) 28 75:=by decide +kernel
  have hfast:StrictAtFast (row 28 75) 28 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 75) 28 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 75) 28 75 hvalid hfast

theorem sr28p76:∀ i ∈ List.range 1,StrictCheckAt 28 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 76) 28 76:=by decide +kernel
  have hfast:StrictAtFast (row 28 76) 28 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 76) 28 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 76) 28 76 hvalid hfast

theorem sr28p77:∀ i ∈ List.range 1,StrictCheckAt 28 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 77) 28 77:=by decide +kernel
  have hfast:StrictAtFast (row 28 77) 28 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 77) 28 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 77) 28 77 hvalid hfast

theorem sr28p78:∀ i ∈ List.range 1,StrictCheckAt 28 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 78) 28 78:=by decide +kernel
  have hfast:StrictAtFast (row 28 78) 28 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 78) 28 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 78) 28 78 hvalid hfast

theorem sr28p79:∀ i ∈ List.range 1,StrictCheckAt 28 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 79) 28 79:=by decide +kernel
  have hfast:StrictAtFast (row 28 79) 28 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 79) 28 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 79) 28 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
