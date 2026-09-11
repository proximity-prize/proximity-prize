import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr23p32:∀ i ∈ List.range 1,StrictCheckAt 23 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 32) 23 32:=by decide +kernel
  have hfast:StrictAtFast (row 23 32) 23 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 32) 23 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 32) 23 32 hvalid hfast

theorem sr23p33:∀ i ∈ List.range 1,StrictCheckAt 23 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 33) 23 33:=by decide +kernel
  have hfast:StrictAtFast (row 23 33) 23 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 33) 23 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 33) 23 33 hvalid hfast

theorem sr23p34:∀ i ∈ List.range 1,StrictCheckAt 23 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 34) 23 34:=by decide +kernel
  have hfast:StrictAtFast (row 23 34) 23 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 34) 23 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 34) 23 34 hvalid hfast

theorem sr23p35:∀ i ∈ List.range 1,StrictCheckAt 23 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 35) 23 35:=by decide +kernel
  have hfast:StrictAtFast (row 23 35) 23 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 35) 23 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 35) 23 35 hvalid hfast

theorem sr23p36:∀ i ∈ List.range 1,StrictCheckAt 23 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 36) 23 36:=by decide +kernel
  have hfast:StrictAtFast (row 23 36) 23 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 36) 23 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 36) 23 36 hvalid hfast

theorem sr23p37:∀ i ∈ List.range 1,StrictCheckAt 23 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 37) 23 37:=by decide +kernel
  have hfast:StrictAtFast (row 23 37) 23 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 37) 23 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 37) 23 37 hvalid hfast

theorem sr23p38:∀ i ∈ List.range 1,StrictCheckAt 23 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 38) 23 38:=by decide +kernel
  have hfast:StrictAtFast (row 23 38) 23 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 38) 23 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 38) 23 38 hvalid hfast

theorem sr23p39:∀ i ∈ List.range 1,StrictCheckAt 23 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 39) 23 39:=by decide +kernel
  have hfast:StrictAtFast (row 23 39) 23 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 39) 23 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 39) 23 39 hvalid hfast

theorem sr23p40:∀ i ∈ List.range 1,StrictCheckAt 23 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 40) 23 40:=by decide +kernel
  have hfast:StrictAtFast (row 23 40) 23 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 40) 23 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 40) 23 40 hvalid hfast

theorem sr23p41:∀ i ∈ List.range 1,StrictCheckAt 23 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 41) 23 41:=by decide +kernel
  have hfast:StrictAtFast (row 23 41) 23 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 41) 23 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 41) 23 41 hvalid hfast

theorem sr23p42:∀ i ∈ List.range 1,StrictCheckAt 23 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 42) 23 42:=by decide +kernel
  have hfast:StrictAtFast (row 23 42) 23 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 42) 23 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 42) 23 42 hvalid hfast

theorem sr23p43:∀ i ∈ List.range 1,StrictCheckAt 23 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 43) 23 43:=by decide +kernel
  have hfast:StrictAtFast (row 23 43) 23 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 43) 23 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 43) 23 43 hvalid hfast

theorem sr23p44:∀ i ∈ List.range 1,StrictCheckAt 23 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 44) 23 44:=by decide +kernel
  have hfast:StrictAtFast (row 23 44) 23 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 44) 23 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 44) 23 44 hvalid hfast

theorem sr23p45:∀ i ∈ List.range 1,StrictCheckAt 23 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 45) 23 45:=by decide +kernel
  have hfast:StrictAtFast (row 23 45) 23 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 45) 23 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 45) 23 45 hvalid hfast

theorem sr23p46:∀ i ∈ List.range 1,StrictCheckAt 23 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 46) 23 46:=by decide +kernel
  have hfast:StrictAtFast (row 23 46) 23 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 46) 23 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 46) 23 46 hvalid hfast

theorem sr23p47:∀ i ∈ List.range 1,StrictCheckAt 23 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 47) 23 47:=by decide +kernel
  have hfast:StrictAtFast (row 23 47) 23 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 47) 23 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 47) 23 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
