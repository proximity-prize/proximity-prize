import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p64:∀ i ∈ List.range 1,StrictCheckAt 14 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 64) 14 64:=by decide +kernel
  have hfast:StrictAtFast (row 14 64) 14 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 64) 14 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 64) 14 64 hvalid hfast

theorem sr14p65:∀ i ∈ List.range 1,StrictCheckAt 14 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 65) 14 65:=by decide +kernel
  have hfast:StrictAtFast (row 14 65) 14 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 65) 14 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 65) 14 65 hvalid hfast

theorem sr14p66:∀ i ∈ List.range 1,StrictCheckAt 14 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 66) 14 66:=by decide +kernel
  have hfast:StrictAtFast (row 14 66) 14 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 66) 14 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 66) 14 66 hvalid hfast

theorem sr14p67:∀ i ∈ List.range 1,StrictCheckAt 14 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 67) 14 67:=by decide +kernel
  have hfast:StrictAtFast (row 14 67) 14 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 67) 14 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 67) 14 67 hvalid hfast

theorem sr14p68:∀ i ∈ List.range 1,StrictCheckAt 14 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 68) 14 68:=by decide +kernel
  have hfast:StrictAtFast (row 14 68) 14 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 68) 14 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 68) 14 68 hvalid hfast

theorem sr14p69:∀ i ∈ List.range 1,StrictCheckAt 14 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 69) 14 69:=by decide +kernel
  have hfast:StrictAtFast (row 14 69) 14 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 69) 14 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 69) 14 69 hvalid hfast

theorem sr14p70:∀ i ∈ List.range 1,StrictCheckAt 14 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 70) 14 70:=by decide +kernel
  have hfast:StrictAtFast (row 14 70) 14 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 70) 14 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 70) 14 70 hvalid hfast

theorem sr14p71:∀ i ∈ List.range 1,StrictCheckAt 14 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 71) 14 71:=by decide +kernel
  have hfast:StrictAtFast (row 14 71) 14 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 71) 14 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 71) 14 71 hvalid hfast

theorem sr14p72:∀ i ∈ List.range 1,StrictCheckAt 14 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 72) 14 72:=by decide +kernel
  have hfast:StrictAtFast (row 14 72) 14 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 72) 14 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 72) 14 72 hvalid hfast

theorem sr14p73:∀ i ∈ List.range 1,StrictCheckAt 14 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 73) 14 73:=by decide +kernel
  have hfast:StrictAtFast (row 14 73) 14 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 73) 14 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 73) 14 73 hvalid hfast

theorem sr14p74:∀ i ∈ List.range 1,StrictCheckAt 14 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 74) 14 74:=by decide +kernel
  have hfast:StrictAtFast (row 14 74) 14 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 74) 14 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 74) 14 74 hvalid hfast

theorem sr14p75:∀ i ∈ List.range 1,StrictCheckAt 14 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 75) 14 75:=by decide +kernel
  have hfast:StrictAtFast (row 14 75) 14 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 75) 14 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 75) 14 75 hvalid hfast

theorem sr14p76:∀ i ∈ List.range 1,StrictCheckAt 14 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 76) 14 76:=by decide +kernel
  have hfast:StrictAtFast (row 14 76) 14 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 76) 14 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 76) 14 76 hvalid hfast

theorem sr14p77:∀ i ∈ List.range 1,StrictCheckAt 14 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 77) 14 77:=by decide +kernel
  have hfast:StrictAtFast (row 14 77) 14 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 77) 14 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 77) 14 77 hvalid hfast

theorem sr14p78:∀ i ∈ List.range 1,StrictCheckAt 14 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 78) 14 78:=by decide +kernel
  have hfast:StrictAtFast (row 14 78) 14 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 78) 14 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 78) 14 78 hvalid hfast

theorem sr14p79:∀ i ∈ List.range 1,StrictCheckAt 14 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 79) 14 79:=by decide +kernel
  have hfast:StrictAtFast (row 14 79) 14 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 79) 14 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 79) 14 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
