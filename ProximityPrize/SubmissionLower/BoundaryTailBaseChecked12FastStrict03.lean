import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr12p32:∀ i ∈ List.range 1,StrictCheckAt 12 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 32) 12 32:=by decide +kernel
  have hfast:StrictAtFast (row 12 32) 12 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 32) 12 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 32) 12 32 hvalid hfast

theorem sr12p33:∀ i ∈ List.range 1,StrictCheckAt 12 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 33) 12 33:=by decide +kernel
  have hfast:StrictAtFast (row 12 33) 12 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 33) 12 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 33) 12 33 hvalid hfast

theorem sr12p34:∀ i ∈ List.range 1,StrictCheckAt 12 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 34) 12 34:=by decide +kernel
  have hfast:StrictAtFast (row 12 34) 12 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 34) 12 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 34) 12 34 hvalid hfast

theorem sr12p35:∀ i ∈ List.range 1,StrictCheckAt 12 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 35) 12 35:=by decide +kernel
  have hfast:StrictAtFast (row 12 35) 12 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 35) 12 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 35) 12 35 hvalid hfast

theorem sr12p36:∀ i ∈ List.range 1,StrictCheckAt 12 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 36) 12 36:=by decide +kernel
  have hfast:StrictAtFast (row 12 36) 12 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 36) 12 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 36) 12 36 hvalid hfast

theorem sr12p37:∀ i ∈ List.range 1,StrictCheckAt 12 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 37) 12 37:=by decide +kernel
  have hfast:StrictAtFast (row 12 37) 12 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 37) 12 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 37) 12 37 hvalid hfast

theorem sr12p38:∀ i ∈ List.range 1,StrictCheckAt 12 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 38) 12 38:=by decide +kernel
  have hfast:StrictAtFast (row 12 38) 12 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 38) 12 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 38) 12 38 hvalid hfast

theorem sr12p39:∀ i ∈ List.range 1,StrictCheckAt 12 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 39) 12 39:=by decide +kernel
  have hfast:StrictAtFast (row 12 39) 12 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 39) 12 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 39) 12 39 hvalid hfast

theorem sr12p40:∀ i ∈ List.range 1,StrictCheckAt 12 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 40) 12 40:=by decide +kernel
  have hfast:StrictAtFast (row 12 40) 12 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 40) 12 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 40) 12 40 hvalid hfast

theorem sr12p41:∀ i ∈ List.range 1,StrictCheckAt 12 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 41) 12 41:=by decide +kernel
  have hfast:StrictAtFast (row 12 41) 12 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 41) 12 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 41) 12 41 hvalid hfast

theorem sr12p42:∀ i ∈ List.range 1,StrictCheckAt 12 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 42) 12 42:=by decide +kernel
  have hfast:StrictAtFast (row 12 42) 12 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 42) 12 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 42) 12 42 hvalid hfast

theorem sr12p43:∀ i ∈ List.range 1,StrictCheckAt 12 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 43) 12 43:=by decide +kernel
  have hfast:StrictAtFast (row 12 43) 12 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 43) 12 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 43) 12 43 hvalid hfast

theorem sr12p44:∀ i ∈ List.range 1,StrictCheckAt 12 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 44) 12 44:=by decide +kernel
  have hfast:StrictAtFast (row 12 44) 12 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 44) 12 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 44) 12 44 hvalid hfast

theorem sr12p45:∀ i ∈ List.range 1,StrictCheckAt 12 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 45) 12 45:=by decide +kernel
  have hfast:StrictAtFast (row 12 45) 12 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 45) 12 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 45) 12 45 hvalid hfast

theorem sr12p46:∀ i ∈ List.range 1,StrictCheckAt 12 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 46) 12 46:=by decide +kernel
  have hfast:StrictAtFast (row 12 46) 12 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 46) 12 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 46) 12 46 hvalid hfast

theorem sr12p47:∀ i ∈ List.range 1,StrictCheckAt 12 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 47) 12 47:=by decide +kernel
  have hfast:StrictAtFast (row 12 47) 12 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 47) 12 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 47) 12 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
