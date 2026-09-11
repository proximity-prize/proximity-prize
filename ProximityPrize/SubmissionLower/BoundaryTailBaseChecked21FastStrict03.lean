import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr21p32:∀ i ∈ List.range 1,StrictCheckAt 21 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 32) 21 32:=by decide +kernel
  have hfast:StrictAtFast (row 21 32) 21 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 32) 21 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 32) 21 32 hvalid hfast

theorem sr21p33:∀ i ∈ List.range 1,StrictCheckAt 21 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 33) 21 33:=by decide +kernel
  have hfast:StrictAtFast (row 21 33) 21 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 33) 21 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 33) 21 33 hvalid hfast

theorem sr21p34:∀ i ∈ List.range 1,StrictCheckAt 21 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 34) 21 34:=by decide +kernel
  have hfast:StrictAtFast (row 21 34) 21 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 34) 21 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 34) 21 34 hvalid hfast

theorem sr21p35:∀ i ∈ List.range 1,StrictCheckAt 21 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 35) 21 35:=by decide +kernel
  have hfast:StrictAtFast (row 21 35) 21 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 35) 21 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 35) 21 35 hvalid hfast

theorem sr21p36:∀ i ∈ List.range 1,StrictCheckAt 21 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 36) 21 36:=by decide +kernel
  have hfast:StrictAtFast (row 21 36) 21 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 36) 21 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 36) 21 36 hvalid hfast

theorem sr21p37:∀ i ∈ List.range 1,StrictCheckAt 21 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 37) 21 37:=by decide +kernel
  have hfast:StrictAtFast (row 21 37) 21 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 37) 21 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 37) 21 37 hvalid hfast

theorem sr21p38:∀ i ∈ List.range 1,StrictCheckAt 21 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 38) 21 38:=by decide +kernel
  have hfast:StrictAtFast (row 21 38) 21 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 38) 21 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 38) 21 38 hvalid hfast

theorem sr21p39:∀ i ∈ List.range 1,StrictCheckAt 21 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 39) 21 39:=by decide +kernel
  have hfast:StrictAtFast (row 21 39) 21 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 39) 21 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 39) 21 39 hvalid hfast

theorem sr21p40:∀ i ∈ List.range 1,StrictCheckAt 21 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 40) 21 40:=by decide +kernel
  have hfast:StrictAtFast (row 21 40) 21 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 40) 21 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 40) 21 40 hvalid hfast

theorem sr21p41:∀ i ∈ List.range 1,StrictCheckAt 21 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 41) 21 41:=by decide +kernel
  have hfast:StrictAtFast (row 21 41) 21 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 41) 21 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 41) 21 41 hvalid hfast

theorem sr21p42:∀ i ∈ List.range 1,StrictCheckAt 21 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 42) 21 42:=by decide +kernel
  have hfast:StrictAtFast (row 21 42) 21 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 42) 21 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 42) 21 42 hvalid hfast

theorem sr21p43:∀ i ∈ List.range 1,StrictCheckAt 21 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 43) 21 43:=by decide +kernel
  have hfast:StrictAtFast (row 21 43) 21 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 43) 21 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 43) 21 43 hvalid hfast

theorem sr21p44:∀ i ∈ List.range 1,StrictCheckAt 21 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 44) 21 44:=by decide +kernel
  have hfast:StrictAtFast (row 21 44) 21 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 44) 21 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 44) 21 44 hvalid hfast

theorem sr21p45:∀ i ∈ List.range 1,StrictCheckAt 21 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 45) 21 45:=by decide +kernel
  have hfast:StrictAtFast (row 21 45) 21 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 45) 21 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 45) 21 45 hvalid hfast

theorem sr21p46:∀ i ∈ List.range 1,StrictCheckAt 21 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 46) 21 46:=by decide +kernel
  have hfast:StrictAtFast (row 21 46) 21 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 46) 21 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 46) 21 46 hvalid hfast

theorem sr21p47:∀ i ∈ List.range 1,StrictCheckAt 21 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 47) 21 47:=by decide +kernel
  have hfast:StrictAtFast (row 21 47) 21 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 47) 21 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 47) 21 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
