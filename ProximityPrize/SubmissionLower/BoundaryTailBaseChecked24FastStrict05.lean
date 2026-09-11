import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr24p64:∀ i ∈ List.range 1,StrictCheckAt 24 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 64) 24 64:=by decide +kernel
  have hfast:StrictAtFast (row 24 64) 24 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 64) 24 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 64) 24 64 hvalid hfast

theorem sr24p65:∀ i ∈ List.range 1,StrictCheckAt 24 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 65) 24 65:=by decide +kernel
  have hfast:StrictAtFast (row 24 65) 24 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 65) 24 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 65) 24 65 hvalid hfast

theorem sr24p66:∀ i ∈ List.range 1,StrictCheckAt 24 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 66) 24 66:=by decide +kernel
  have hfast:StrictAtFast (row 24 66) 24 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 66) 24 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 66) 24 66 hvalid hfast

theorem sr24p67:∀ i ∈ List.range 1,StrictCheckAt 24 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 67) 24 67:=by decide +kernel
  have hfast:StrictAtFast (row 24 67) 24 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 67) 24 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 67) 24 67 hvalid hfast

theorem sr24p68:∀ i ∈ List.range 1,StrictCheckAt 24 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 68) 24 68:=by decide +kernel
  have hfast:StrictAtFast (row 24 68) 24 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 68) 24 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 68) 24 68 hvalid hfast

theorem sr24p69:∀ i ∈ List.range 1,StrictCheckAt 24 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 69) 24 69:=by decide +kernel
  have hfast:StrictAtFast (row 24 69) 24 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 69) 24 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 69) 24 69 hvalid hfast

theorem sr24p70:∀ i ∈ List.range 1,StrictCheckAt 24 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 70) 24 70:=by decide +kernel
  have hfast:StrictAtFast (row 24 70) 24 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 70) 24 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 70) 24 70 hvalid hfast

theorem sr24p71:∀ i ∈ List.range 1,StrictCheckAt 24 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 71) 24 71:=by decide +kernel
  have hfast:StrictAtFast (row 24 71) 24 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 71) 24 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 71) 24 71 hvalid hfast

theorem sr24p72:∀ i ∈ List.range 1,StrictCheckAt 24 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 72) 24 72:=by decide +kernel
  have hfast:StrictAtFast (row 24 72) 24 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 72) 24 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 72) 24 72 hvalid hfast

theorem sr24p73:∀ i ∈ List.range 1,StrictCheckAt 24 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 73) 24 73:=by decide +kernel
  have hfast:StrictAtFast (row 24 73) 24 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 73) 24 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 73) 24 73 hvalid hfast

theorem sr24p74:∀ i ∈ List.range 1,StrictCheckAt 24 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 74) 24 74:=by decide +kernel
  have hfast:StrictAtFast (row 24 74) 24 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 74) 24 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 74) 24 74 hvalid hfast

theorem sr24p75:∀ i ∈ List.range 1,StrictCheckAt 24 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 75) 24 75:=by decide +kernel
  have hfast:StrictAtFast (row 24 75) 24 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 75) 24 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 75) 24 75 hvalid hfast

theorem sr24p76:∀ i ∈ List.range 1,StrictCheckAt 24 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 76) 24 76:=by decide +kernel
  have hfast:StrictAtFast (row 24 76) 24 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 76) 24 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 76) 24 76 hvalid hfast

theorem sr24p77:∀ i ∈ List.range 1,StrictCheckAt 24 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 77) 24 77:=by decide +kernel
  have hfast:StrictAtFast (row 24 77) 24 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 77) 24 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 77) 24 77 hvalid hfast

theorem sr24p78:∀ i ∈ List.range 1,StrictCheckAt 24 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 78) 24 78:=by decide +kernel
  have hfast:StrictAtFast (row 24 78) 24 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 78) 24 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 78) 24 78 hvalid hfast

theorem sr24p79:∀ i ∈ List.range 1,StrictCheckAt 24 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 79) 24 79:=by decide +kernel
  have hfast:StrictAtFast (row 24 79) 24 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 79) 24 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 79) 24 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
