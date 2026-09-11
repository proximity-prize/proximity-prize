import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr26p32:∀ i ∈ List.range 1,StrictCheckAt 26 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 32) 26 32:=by decide +kernel
  have hfast:StrictAtFast (row 26 32) 26 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 32) 26 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 32) 26 32 hvalid hfast

theorem sr26p33:∀ i ∈ List.range 1,StrictCheckAt 26 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 33) 26 33:=by decide +kernel
  have hfast:StrictAtFast (row 26 33) 26 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 33) 26 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 33) 26 33 hvalid hfast

theorem sr26p34:∀ i ∈ List.range 1,StrictCheckAt 26 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 34) 26 34:=by decide +kernel
  have hfast:StrictAtFast (row 26 34) 26 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 34) 26 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 34) 26 34 hvalid hfast

theorem sr26p35:∀ i ∈ List.range 1,StrictCheckAt 26 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 35) 26 35:=by decide +kernel
  have hfast:StrictAtFast (row 26 35) 26 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 35) 26 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 35) 26 35 hvalid hfast

theorem sr26p36:∀ i ∈ List.range 1,StrictCheckAt 26 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 36) 26 36:=by decide +kernel
  have hfast:StrictAtFast (row 26 36) 26 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 36) 26 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 36) 26 36 hvalid hfast

theorem sr26p37:∀ i ∈ List.range 1,StrictCheckAt 26 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 37) 26 37:=by decide +kernel
  have hfast:StrictAtFast (row 26 37) 26 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 37) 26 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 37) 26 37 hvalid hfast

theorem sr26p38:∀ i ∈ List.range 1,StrictCheckAt 26 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 38) 26 38:=by decide +kernel
  have hfast:StrictAtFast (row 26 38) 26 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 38) 26 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 38) 26 38 hvalid hfast

theorem sr26p39:∀ i ∈ List.range 1,StrictCheckAt 26 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 39) 26 39:=by decide +kernel
  have hfast:StrictAtFast (row 26 39) 26 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 39) 26 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 39) 26 39 hvalid hfast

theorem sr26p40:∀ i ∈ List.range 1,StrictCheckAt 26 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 40) 26 40:=by decide +kernel
  have hfast:StrictAtFast (row 26 40) 26 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 40) 26 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 40) 26 40 hvalid hfast

theorem sr26p41:∀ i ∈ List.range 1,StrictCheckAt 26 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 41) 26 41:=by decide +kernel
  have hfast:StrictAtFast (row 26 41) 26 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 41) 26 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 41) 26 41 hvalid hfast

theorem sr26p42:∀ i ∈ List.range 1,StrictCheckAt 26 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 42) 26 42:=by decide +kernel
  have hfast:StrictAtFast (row 26 42) 26 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 42) 26 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 42) 26 42 hvalid hfast

theorem sr26p43:∀ i ∈ List.range 1,StrictCheckAt 26 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 43) 26 43:=by decide +kernel
  have hfast:StrictAtFast (row 26 43) 26 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 43) 26 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 43) 26 43 hvalid hfast

theorem sr26p44:∀ i ∈ List.range 1,StrictCheckAt 26 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 44) 26 44:=by decide +kernel
  have hfast:StrictAtFast (row 26 44) 26 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 44) 26 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 44) 26 44 hvalid hfast

theorem sr26p45:∀ i ∈ List.range 1,StrictCheckAt 26 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 45) 26 45:=by decide +kernel
  have hfast:StrictAtFast (row 26 45) 26 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 45) 26 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 45) 26 45 hvalid hfast

theorem sr26p46:∀ i ∈ List.range 1,StrictCheckAt 26 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 46) 26 46:=by decide +kernel
  have hfast:StrictAtFast (row 26 46) 26 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 46) 26 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 46) 26 46 hvalid hfast

theorem sr26p47:∀ i ∈ List.range 1,StrictCheckAt 26 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 47) 26 47:=by decide +kernel
  have hfast:StrictAtFast (row 26 47) 26 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 47) 26 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 47) 26 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
