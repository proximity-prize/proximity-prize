import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr7p32:∀ i ∈ List.range 1,StrictCheckAt 7 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 32) 7 32:=by decide +kernel
  have hfast:StrictAtFast (row 7 32) 7 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 32) 7 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 32) 7 32 hvalid hfast

theorem sr7p33:∀ i ∈ List.range 1,StrictCheckAt 7 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 33) 7 33:=by decide +kernel
  have hfast:StrictAtFast (row 7 33) 7 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 33) 7 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 33) 7 33 hvalid hfast

theorem sr7p34:∀ i ∈ List.range 1,StrictCheckAt 7 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 34) 7 34:=by decide +kernel
  have hfast:StrictAtFast (row 7 34) 7 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 34) 7 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 34) 7 34 hvalid hfast

theorem sr7p35:∀ i ∈ List.range 1,StrictCheckAt 7 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 35) 7 35:=by decide +kernel
  have hfast:StrictAtFast (row 7 35) 7 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 35) 7 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 35) 7 35 hvalid hfast

theorem sr7p36:∀ i ∈ List.range 1,StrictCheckAt 7 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 36) 7 36:=by decide +kernel
  have hfast:StrictAtFast (row 7 36) 7 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 36) 7 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 36) 7 36 hvalid hfast

theorem sr7p37:∀ i ∈ List.range 1,StrictCheckAt 7 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 37) 7 37:=by decide +kernel
  have hfast:StrictAtFast (row 7 37) 7 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 37) 7 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 37) 7 37 hvalid hfast

theorem sr7p38:∀ i ∈ List.range 1,StrictCheckAt 7 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 38) 7 38:=by decide +kernel
  have hfast:StrictAtFast (row 7 38) 7 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 38) 7 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 38) 7 38 hvalid hfast

theorem sr7p39:∀ i ∈ List.range 1,StrictCheckAt 7 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 39) 7 39:=by decide +kernel
  have hfast:StrictAtFast (row 7 39) 7 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 39) 7 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 39) 7 39 hvalid hfast

theorem sr7p40:∀ i ∈ List.range 1,StrictCheckAt 7 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 40) 7 40:=by decide +kernel
  have hfast:StrictAtFast (row 7 40) 7 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 40) 7 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 40) 7 40 hvalid hfast

theorem sr7p41:∀ i ∈ List.range 1,StrictCheckAt 7 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 41) 7 41:=by decide +kernel
  have hfast:StrictAtFast (row 7 41) 7 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 41) 7 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 41) 7 41 hvalid hfast

theorem sr7p42:∀ i ∈ List.range 1,StrictCheckAt 7 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 42) 7 42:=by decide +kernel
  have hfast:StrictAtFast (row 7 42) 7 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 42) 7 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 42) 7 42 hvalid hfast

theorem sr7p43:∀ i ∈ List.range 1,StrictCheckAt 7 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 43) 7 43:=by decide +kernel
  have hfast:StrictAtFast (row 7 43) 7 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 43) 7 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 43) 7 43 hvalid hfast

theorem sr7p44:∀ i ∈ List.range 1,StrictCheckAt 7 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 44) 7 44:=by decide +kernel
  have hfast:StrictAtFast (row 7 44) 7 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 44) 7 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 44) 7 44 hvalid hfast

theorem sr7p45:∀ i ∈ List.range 1,StrictCheckAt 7 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 45) 7 45:=by decide +kernel
  have hfast:StrictAtFast (row 7 45) 7 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 45) 7 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 45) 7 45 hvalid hfast

theorem sr7p46:∀ i ∈ List.range 1,StrictCheckAt 7 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 46) 7 46:=by decide +kernel
  have hfast:StrictAtFast (row 7 46) 7 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 46) 7 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 46) 7 46 hvalid hfast

theorem sr7p47:∀ i ∈ List.range 1,StrictCheckAt 7 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 47) 7 47:=by decide +kernel
  have hfast:StrictAtFast (row 7 47) 7 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 47) 7 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 47) 7 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
