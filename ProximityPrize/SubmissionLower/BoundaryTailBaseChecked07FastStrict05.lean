import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr7p64:∀ i ∈ List.range 1,StrictCheckAt 7 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 64) 7 64:=by decide +kernel
  have hfast:StrictAtFast (row 7 64) 7 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 64) 7 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 64) 7 64 hvalid hfast

theorem sr7p65:∀ i ∈ List.range 1,StrictCheckAt 7 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 65) 7 65:=by decide +kernel
  have hfast:StrictAtFast (row 7 65) 7 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 65) 7 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 65) 7 65 hvalid hfast

theorem sr7p66:∀ i ∈ List.range 1,StrictCheckAt 7 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 66) 7 66:=by decide +kernel
  have hfast:StrictAtFast (row 7 66) 7 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 66) 7 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 66) 7 66 hvalid hfast

theorem sr7p67:∀ i ∈ List.range 1,StrictCheckAt 7 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 67) 7 67:=by decide +kernel
  have hfast:StrictAtFast (row 7 67) 7 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 67) 7 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 67) 7 67 hvalid hfast

theorem sr7p68:∀ i ∈ List.range 1,StrictCheckAt 7 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 68) 7 68:=by decide +kernel
  have hfast:StrictAtFast (row 7 68) 7 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 68) 7 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 68) 7 68 hvalid hfast

theorem sr7p69:∀ i ∈ List.range 1,StrictCheckAt 7 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 69) 7 69:=by decide +kernel
  have hfast:StrictAtFast (row 7 69) 7 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 69) 7 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 69) 7 69 hvalid hfast

theorem sr7p70:∀ i ∈ List.range 1,StrictCheckAt 7 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 70) 7 70:=by decide +kernel
  have hfast:StrictAtFast (row 7 70) 7 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 70) 7 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 70) 7 70 hvalid hfast

theorem sr7p71:∀ i ∈ List.range 1,StrictCheckAt 7 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 71) 7 71:=by decide +kernel
  have hfast:StrictAtFast (row 7 71) 7 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 71) 7 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 71) 7 71 hvalid hfast

theorem sr7p72:∀ i ∈ List.range 1,StrictCheckAt 7 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 72) 7 72:=by decide +kernel
  have hfast:StrictAtFast (row 7 72) 7 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 72) 7 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 72) 7 72 hvalid hfast

theorem sr7p73:∀ i ∈ List.range 1,StrictCheckAt 7 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 73) 7 73:=by decide +kernel
  have hfast:StrictAtFast (row 7 73) 7 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 73) 7 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 73) 7 73 hvalid hfast

theorem sr7p74:∀ i ∈ List.range 1,StrictCheckAt 7 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 74) 7 74:=by decide +kernel
  have hfast:StrictAtFast (row 7 74) 7 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 74) 7 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 74) 7 74 hvalid hfast

theorem sr7p75:∀ i ∈ List.range 1,StrictCheckAt 7 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 75) 7 75:=by decide +kernel
  have hfast:StrictAtFast (row 7 75) 7 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 75) 7 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 75) 7 75 hvalid hfast

theorem sr7p76:∀ i ∈ List.range 1,StrictCheckAt 7 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 76) 7 76:=by decide +kernel
  have hfast:StrictAtFast (row 7 76) 7 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 76) 7 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 76) 7 76 hvalid hfast

theorem sr7p77:∀ i ∈ List.range 1,StrictCheckAt 7 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 77) 7 77:=by decide +kernel
  have hfast:StrictAtFast (row 7 77) 7 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 77) 7 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 77) 7 77 hvalid hfast

theorem sr7p78:∀ i ∈ List.range 1,StrictCheckAt 7 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 78) 7 78:=by decide +kernel
  have hfast:StrictAtFast (row 7 78) 7 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 78) 7 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 78) 7 78 hvalid hfast

theorem sr7p79:∀ i ∈ List.range 1,StrictCheckAt 7 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 79) 7 79:=by decide +kernel
  have hfast:StrictAtFast (row 7 79) 7 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 79) 7 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 79) 7 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
