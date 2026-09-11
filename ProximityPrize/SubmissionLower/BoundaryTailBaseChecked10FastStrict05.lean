import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p64:∀ i ∈ List.range 1,StrictCheckAt 10 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 64) 10 64:=by decide +kernel
  have hfast:StrictAtFast (row 10 64) 10 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 64) 10 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 64) 10 64 hvalid hfast

theorem sr10p65:∀ i ∈ List.range 1,StrictCheckAt 10 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 65) 10 65:=by decide +kernel
  have hfast:StrictAtFast (row 10 65) 10 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 65) 10 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 65) 10 65 hvalid hfast

theorem sr10p66:∀ i ∈ List.range 1,StrictCheckAt 10 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 66) 10 66:=by decide +kernel
  have hfast:StrictAtFast (row 10 66) 10 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 66) 10 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 66) 10 66 hvalid hfast

theorem sr10p67:∀ i ∈ List.range 1,StrictCheckAt 10 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 67) 10 67:=by decide +kernel
  have hfast:StrictAtFast (row 10 67) 10 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 67) 10 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 67) 10 67 hvalid hfast

theorem sr10p68:∀ i ∈ List.range 1,StrictCheckAt 10 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 68) 10 68:=by decide +kernel
  have hfast:StrictAtFast (row 10 68) 10 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 68) 10 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 68) 10 68 hvalid hfast

theorem sr10p69:∀ i ∈ List.range 1,StrictCheckAt 10 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 69) 10 69:=by decide +kernel
  have hfast:StrictAtFast (row 10 69) 10 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 69) 10 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 69) 10 69 hvalid hfast

theorem sr10p70:∀ i ∈ List.range 1,StrictCheckAt 10 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 70) 10 70:=by decide +kernel
  have hfast:StrictAtFast (row 10 70) 10 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 70) 10 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 70) 10 70 hvalid hfast

theorem sr10p71:∀ i ∈ List.range 1,StrictCheckAt 10 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 71) 10 71:=by decide +kernel
  have hfast:StrictAtFast (row 10 71) 10 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 71) 10 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 71) 10 71 hvalid hfast

theorem sr10p72:∀ i ∈ List.range 1,StrictCheckAt 10 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 72) 10 72:=by decide +kernel
  have hfast:StrictAtFast (row 10 72) 10 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 72) 10 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 72) 10 72 hvalid hfast

theorem sr10p73:∀ i ∈ List.range 1,StrictCheckAt 10 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 73) 10 73:=by decide +kernel
  have hfast:StrictAtFast (row 10 73) 10 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 73) 10 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 73) 10 73 hvalid hfast

theorem sr10p74:∀ i ∈ List.range 1,StrictCheckAt 10 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 74) 10 74:=by decide +kernel
  have hfast:StrictAtFast (row 10 74) 10 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 74) 10 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 74) 10 74 hvalid hfast

theorem sr10p75:∀ i ∈ List.range 1,StrictCheckAt 10 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 75) 10 75:=by decide +kernel
  have hfast:StrictAtFast (row 10 75) 10 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 75) 10 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 75) 10 75 hvalid hfast

theorem sr10p76:∀ i ∈ List.range 1,StrictCheckAt 10 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 76) 10 76:=by decide +kernel
  have hfast:StrictAtFast (row 10 76) 10 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 76) 10 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 76) 10 76 hvalid hfast

theorem sr10p77:∀ i ∈ List.range 1,StrictCheckAt 10 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 77) 10 77:=by decide +kernel
  have hfast:StrictAtFast (row 10 77) 10 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 77) 10 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 77) 10 77 hvalid hfast

theorem sr10p78:∀ i ∈ List.range 1,StrictCheckAt 10 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 78) 10 78:=by decide +kernel
  have hfast:StrictAtFast (row 10 78) 10 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 78) 10 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 78) 10 78 hvalid hfast

theorem sr10p79:∀ i ∈ List.range 1,StrictCheckAt 10 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 79) 10 79:=by decide +kernel
  have hfast:StrictAtFast (row 10 79) 10 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 79) 10 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 79) 10 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
