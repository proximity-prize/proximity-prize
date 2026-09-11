import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr20p32:∀ i ∈ List.range 1,StrictCheckAt 20 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 32) 20 32:=by decide +kernel
  have hfast:StrictAtFast (row 20 32) 20 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 32) 20 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 32) 20 32 hvalid hfast

theorem sr20p33:∀ i ∈ List.range 1,StrictCheckAt 20 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 33) 20 33:=by decide +kernel
  have hfast:StrictAtFast (row 20 33) 20 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 33) 20 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 33) 20 33 hvalid hfast

theorem sr20p34:∀ i ∈ List.range 1,StrictCheckAt 20 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 34) 20 34:=by decide +kernel
  have hfast:StrictAtFast (row 20 34) 20 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 34) 20 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 34) 20 34 hvalid hfast

theorem sr20p35:∀ i ∈ List.range 1,StrictCheckAt 20 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 35) 20 35:=by decide +kernel
  have hfast:StrictAtFast (row 20 35) 20 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 35) 20 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 35) 20 35 hvalid hfast

theorem sr20p36:∀ i ∈ List.range 1,StrictCheckAt 20 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 36) 20 36:=by decide +kernel
  have hfast:StrictAtFast (row 20 36) 20 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 36) 20 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 36) 20 36 hvalid hfast

theorem sr20p37:∀ i ∈ List.range 1,StrictCheckAt 20 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 37) 20 37:=by decide +kernel
  have hfast:StrictAtFast (row 20 37) 20 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 37) 20 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 37) 20 37 hvalid hfast

theorem sr20p38:∀ i ∈ List.range 1,StrictCheckAt 20 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 38) 20 38:=by decide +kernel
  have hfast:StrictAtFast (row 20 38) 20 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 38) 20 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 38) 20 38 hvalid hfast

theorem sr20p39:∀ i ∈ List.range 1,StrictCheckAt 20 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 39) 20 39:=by decide +kernel
  have hfast:StrictAtFast (row 20 39) 20 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 39) 20 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 39) 20 39 hvalid hfast

theorem sr20p40:∀ i ∈ List.range 1,StrictCheckAt 20 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 40) 20 40:=by decide +kernel
  have hfast:StrictAtFast (row 20 40) 20 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 40) 20 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 40) 20 40 hvalid hfast

theorem sr20p41:∀ i ∈ List.range 1,StrictCheckAt 20 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 41) 20 41:=by decide +kernel
  have hfast:StrictAtFast (row 20 41) 20 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 41) 20 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 41) 20 41 hvalid hfast

theorem sr20p42:∀ i ∈ List.range 1,StrictCheckAt 20 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 42) 20 42:=by decide +kernel
  have hfast:StrictAtFast (row 20 42) 20 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 42) 20 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 42) 20 42 hvalid hfast

theorem sr20p43:∀ i ∈ List.range 1,StrictCheckAt 20 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 43) 20 43:=by decide +kernel
  have hfast:StrictAtFast (row 20 43) 20 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 43) 20 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 43) 20 43 hvalid hfast

theorem sr20p44:∀ i ∈ List.range 1,StrictCheckAt 20 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 44) 20 44:=by decide +kernel
  have hfast:StrictAtFast (row 20 44) 20 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 44) 20 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 44) 20 44 hvalid hfast

theorem sr20p45:∀ i ∈ List.range 1,StrictCheckAt 20 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 45) 20 45:=by decide +kernel
  have hfast:StrictAtFast (row 20 45) 20 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 45) 20 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 45) 20 45 hvalid hfast

theorem sr20p46:∀ i ∈ List.range 1,StrictCheckAt 20 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 46) 20 46:=by decide +kernel
  have hfast:StrictAtFast (row 20 46) 20 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 46) 20 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 46) 20 46 hvalid hfast

theorem sr20p47:∀ i ∈ List.range 1,StrictCheckAt 20 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 47) 20 47:=by decide +kernel
  have hfast:StrictAtFast (row 20 47) 20 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 47) 20 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 47) 20 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
