import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr28p32:∀ i ∈ List.range 1,StrictCheckAt 28 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 32) 28 32:=by decide +kernel
  have hfast:StrictAtFast (row 28 32) 28 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 32) 28 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 32) 28 32 hvalid hfast

theorem sr28p33:∀ i ∈ List.range 1,StrictCheckAt 28 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 33) 28 33:=by decide +kernel
  have hfast:StrictAtFast (row 28 33) 28 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 33) 28 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 33) 28 33 hvalid hfast

theorem sr28p34:∀ i ∈ List.range 1,StrictCheckAt 28 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 34) 28 34:=by decide +kernel
  have hfast:StrictAtFast (row 28 34) 28 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 34) 28 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 34) 28 34 hvalid hfast

theorem sr28p35:∀ i ∈ List.range 1,StrictCheckAt 28 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 35) 28 35:=by decide +kernel
  have hfast:StrictAtFast (row 28 35) 28 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 35) 28 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 35) 28 35 hvalid hfast

theorem sr28p36:∀ i ∈ List.range 1,StrictCheckAt 28 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 36) 28 36:=by decide +kernel
  have hfast:StrictAtFast (row 28 36) 28 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 36) 28 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 36) 28 36 hvalid hfast

theorem sr28p37:∀ i ∈ List.range 1,StrictCheckAt 28 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 37) 28 37:=by decide +kernel
  have hfast:StrictAtFast (row 28 37) 28 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 37) 28 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 37) 28 37 hvalid hfast

theorem sr28p38:∀ i ∈ List.range 1,StrictCheckAt 28 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 38) 28 38:=by decide +kernel
  have hfast:StrictAtFast (row 28 38) 28 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 38) 28 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 38) 28 38 hvalid hfast

theorem sr28p39:∀ i ∈ List.range 1,StrictCheckAt 28 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 39) 28 39:=by decide +kernel
  have hfast:StrictAtFast (row 28 39) 28 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 39) 28 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 39) 28 39 hvalid hfast

theorem sr28p40:∀ i ∈ List.range 1,StrictCheckAt 28 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 40) 28 40:=by decide +kernel
  have hfast:StrictAtFast (row 28 40) 28 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 40) 28 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 40) 28 40 hvalid hfast

theorem sr28p41:∀ i ∈ List.range 1,StrictCheckAt 28 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 41) 28 41:=by decide +kernel
  have hfast:StrictAtFast (row 28 41) 28 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 41) 28 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 41) 28 41 hvalid hfast

theorem sr28p42:∀ i ∈ List.range 1,StrictCheckAt 28 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 42) 28 42:=by decide +kernel
  have hfast:StrictAtFast (row 28 42) 28 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 42) 28 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 42) 28 42 hvalid hfast

theorem sr28p43:∀ i ∈ List.range 1,StrictCheckAt 28 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 43) 28 43:=by decide +kernel
  have hfast:StrictAtFast (row 28 43) 28 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 43) 28 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 43) 28 43 hvalid hfast

theorem sr28p44:∀ i ∈ List.range 1,StrictCheckAt 28 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 44) 28 44:=by decide +kernel
  have hfast:StrictAtFast (row 28 44) 28 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 44) 28 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 44) 28 44 hvalid hfast

theorem sr28p45:∀ i ∈ List.range 1,StrictCheckAt 28 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 45) 28 45:=by decide +kernel
  have hfast:StrictAtFast (row 28 45) 28 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 45) 28 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 45) 28 45 hvalid hfast

theorem sr28p46:∀ i ∈ List.range 1,StrictCheckAt 28 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 46) 28 46:=by decide +kernel
  have hfast:StrictAtFast (row 28 46) 28 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 46) 28 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 46) 28 46 hvalid hfast

theorem sr28p47:∀ i ∈ List.range 1,StrictCheckAt 28 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 47) 28 47:=by decide +kernel
  have hfast:StrictAtFast (row 28 47) 28 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 47) 28 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 47) 28 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
