import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr11p32:∀ i ∈ List.range 1,StrictCheckAt 11 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 32) 11 32:=by decide +kernel
  have hfast:StrictAtFast (row 11 32) 11 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 32) 11 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 32) 11 32 hvalid hfast

theorem sr11p33:∀ i ∈ List.range 1,StrictCheckAt 11 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 33) 11 33:=by decide +kernel
  have hfast:StrictAtFast (row 11 33) 11 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 33) 11 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 33) 11 33 hvalid hfast

theorem sr11p34:∀ i ∈ List.range 1,StrictCheckAt 11 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 34) 11 34:=by decide +kernel
  have hfast:StrictAtFast (row 11 34) 11 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 34) 11 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 34) 11 34 hvalid hfast

theorem sr11p35:∀ i ∈ List.range 1,StrictCheckAt 11 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 35) 11 35:=by decide +kernel
  have hfast:StrictAtFast (row 11 35) 11 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 35) 11 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 35) 11 35 hvalid hfast

theorem sr11p36:∀ i ∈ List.range 1,StrictCheckAt 11 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 36) 11 36:=by decide +kernel
  have hfast:StrictAtFast (row 11 36) 11 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 36) 11 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 36) 11 36 hvalid hfast

theorem sr11p37:∀ i ∈ List.range 1,StrictCheckAt 11 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 37) 11 37:=by decide +kernel
  have hfast:StrictAtFast (row 11 37) 11 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 37) 11 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 37) 11 37 hvalid hfast

theorem sr11p38:∀ i ∈ List.range 1,StrictCheckAt 11 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 38) 11 38:=by decide +kernel
  have hfast:StrictAtFast (row 11 38) 11 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 38) 11 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 38) 11 38 hvalid hfast

theorem sr11p39:∀ i ∈ List.range 1,StrictCheckAt 11 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 39) 11 39:=by decide +kernel
  have hfast:StrictAtFast (row 11 39) 11 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 39) 11 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 39) 11 39 hvalid hfast

theorem sr11p40:∀ i ∈ List.range 1,StrictCheckAt 11 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 40) 11 40:=by decide +kernel
  have hfast:StrictAtFast (row 11 40) 11 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 40) 11 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 40) 11 40 hvalid hfast

theorem sr11p41:∀ i ∈ List.range 1,StrictCheckAt 11 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 41) 11 41:=by decide +kernel
  have hfast:StrictAtFast (row 11 41) 11 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 41) 11 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 41) 11 41 hvalid hfast

theorem sr11p42:∀ i ∈ List.range 1,StrictCheckAt 11 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 42) 11 42:=by decide +kernel
  have hfast:StrictAtFast (row 11 42) 11 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 42) 11 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 42) 11 42 hvalid hfast

theorem sr11p43:∀ i ∈ List.range 1,StrictCheckAt 11 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 43) 11 43:=by decide +kernel
  have hfast:StrictAtFast (row 11 43) 11 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 43) 11 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 43) 11 43 hvalid hfast

theorem sr11p44:∀ i ∈ List.range 1,StrictCheckAt 11 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 44) 11 44:=by decide +kernel
  have hfast:StrictAtFast (row 11 44) 11 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 44) 11 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 44) 11 44 hvalid hfast

theorem sr11p45:∀ i ∈ List.range 1,StrictCheckAt 11 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 45) 11 45:=by decide +kernel
  have hfast:StrictAtFast (row 11 45) 11 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 45) 11 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 45) 11 45 hvalid hfast

theorem sr11p46:∀ i ∈ List.range 1,StrictCheckAt 11 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 46) 11 46:=by decide +kernel
  have hfast:StrictAtFast (row 11 46) 11 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 46) 11 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 46) 11 46 hvalid hfast

theorem sr11p47:∀ i ∈ List.range 1,StrictCheckAt 11 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 47) 11 47:=by decide +kernel
  have hfast:StrictAtFast (row 11 47) 11 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 47) 11 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 47) 11 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
