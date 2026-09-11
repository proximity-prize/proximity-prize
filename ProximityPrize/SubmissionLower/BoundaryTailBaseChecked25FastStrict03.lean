import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr25p32:∀ i ∈ List.range 1,StrictCheckAt 25 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 32) 25 32:=by decide +kernel
  have hfast:StrictAtFast (row 25 32) 25 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 32) 25 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 32) 25 32 hvalid hfast

theorem sr25p33:∀ i ∈ List.range 1,StrictCheckAt 25 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 33) 25 33:=by decide +kernel
  have hfast:StrictAtFast (row 25 33) 25 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 33) 25 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 33) 25 33 hvalid hfast

theorem sr25p34:∀ i ∈ List.range 1,StrictCheckAt 25 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 34) 25 34:=by decide +kernel
  have hfast:StrictAtFast (row 25 34) 25 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 34) 25 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 34) 25 34 hvalid hfast

theorem sr25p35:∀ i ∈ List.range 1,StrictCheckAt 25 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 35) 25 35:=by decide +kernel
  have hfast:StrictAtFast (row 25 35) 25 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 35) 25 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 35) 25 35 hvalid hfast

theorem sr25p36:∀ i ∈ List.range 1,StrictCheckAt 25 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 36) 25 36:=by decide +kernel
  have hfast:StrictAtFast (row 25 36) 25 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 36) 25 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 36) 25 36 hvalid hfast

theorem sr25p37:∀ i ∈ List.range 1,StrictCheckAt 25 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 37) 25 37:=by decide +kernel
  have hfast:StrictAtFast (row 25 37) 25 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 37) 25 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 37) 25 37 hvalid hfast

theorem sr25p38:∀ i ∈ List.range 1,StrictCheckAt 25 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 38) 25 38:=by decide +kernel
  have hfast:StrictAtFast (row 25 38) 25 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 38) 25 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 38) 25 38 hvalid hfast

theorem sr25p39:∀ i ∈ List.range 1,StrictCheckAt 25 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 39) 25 39:=by decide +kernel
  have hfast:StrictAtFast (row 25 39) 25 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 39) 25 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 39) 25 39 hvalid hfast

theorem sr25p40:∀ i ∈ List.range 1,StrictCheckAt 25 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 40) 25 40:=by decide +kernel
  have hfast:StrictAtFast (row 25 40) 25 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 40) 25 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 40) 25 40 hvalid hfast

theorem sr25p41:∀ i ∈ List.range 1,StrictCheckAt 25 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 41) 25 41:=by decide +kernel
  have hfast:StrictAtFast (row 25 41) 25 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 41) 25 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 41) 25 41 hvalid hfast

theorem sr25p42:∀ i ∈ List.range 1,StrictCheckAt 25 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 42) 25 42:=by decide +kernel
  have hfast:StrictAtFast (row 25 42) 25 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 42) 25 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 42) 25 42 hvalid hfast

theorem sr25p43:∀ i ∈ List.range 1,StrictCheckAt 25 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 43) 25 43:=by decide +kernel
  have hfast:StrictAtFast (row 25 43) 25 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 43) 25 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 43) 25 43 hvalid hfast

theorem sr25p44:∀ i ∈ List.range 1,StrictCheckAt 25 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 44) 25 44:=by decide +kernel
  have hfast:StrictAtFast (row 25 44) 25 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 44) 25 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 44) 25 44 hvalid hfast

theorem sr25p45:∀ i ∈ List.range 1,StrictCheckAt 25 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 45) 25 45:=by decide +kernel
  have hfast:StrictAtFast (row 25 45) 25 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 45) 25 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 45) 25 45 hvalid hfast

theorem sr25p46:∀ i ∈ List.range 1,StrictCheckAt 25 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 46) 25 46:=by decide +kernel
  have hfast:StrictAtFast (row 25 46) 25 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 46) 25 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 46) 25 46 hvalid hfast

theorem sr25p47:∀ i ∈ List.range 1,StrictCheckAt 25 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 47) 25 47:=by decide +kernel
  have hfast:StrictAtFast (row 25 47) 25 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 47) 25 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 47) 25 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
