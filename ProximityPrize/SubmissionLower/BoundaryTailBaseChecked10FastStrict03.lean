import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr10p32:∀ i ∈ List.range 1,StrictCheckAt 10 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 32) 10 32:=by decide +kernel
  have hfast:StrictAtFast (row 10 32) 10 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 32) 10 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 32) 10 32 hvalid hfast

theorem sr10p33:∀ i ∈ List.range 1,StrictCheckAt 10 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 33) 10 33:=by decide +kernel
  have hfast:StrictAtFast (row 10 33) 10 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 33) 10 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 33) 10 33 hvalid hfast

theorem sr10p34:∀ i ∈ List.range 1,StrictCheckAt 10 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 34) 10 34:=by decide +kernel
  have hfast:StrictAtFast (row 10 34) 10 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 34) 10 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 34) 10 34 hvalid hfast

theorem sr10p35:∀ i ∈ List.range 1,StrictCheckAt 10 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 35) 10 35:=by decide +kernel
  have hfast:StrictAtFast (row 10 35) 10 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 35) 10 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 35) 10 35 hvalid hfast

theorem sr10p36:∀ i ∈ List.range 1,StrictCheckAt 10 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 36) 10 36:=by decide +kernel
  have hfast:StrictAtFast (row 10 36) 10 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 36) 10 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 36) 10 36 hvalid hfast

theorem sr10p37:∀ i ∈ List.range 1,StrictCheckAt 10 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 37) 10 37:=by decide +kernel
  have hfast:StrictAtFast (row 10 37) 10 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 37) 10 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 37) 10 37 hvalid hfast

theorem sr10p38:∀ i ∈ List.range 1,StrictCheckAt 10 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 38) 10 38:=by decide +kernel
  have hfast:StrictAtFast (row 10 38) 10 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 38) 10 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 38) 10 38 hvalid hfast

theorem sr10p39:∀ i ∈ List.range 1,StrictCheckAt 10 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 39) 10 39:=by decide +kernel
  have hfast:StrictAtFast (row 10 39) 10 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 39) 10 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 39) 10 39 hvalid hfast

theorem sr10p40:∀ i ∈ List.range 1,StrictCheckAt 10 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 40) 10 40:=by decide +kernel
  have hfast:StrictAtFast (row 10 40) 10 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 40) 10 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 40) 10 40 hvalid hfast

theorem sr10p41:∀ i ∈ List.range 1,StrictCheckAt 10 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 41) 10 41:=by decide +kernel
  have hfast:StrictAtFast (row 10 41) 10 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 41) 10 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 41) 10 41 hvalid hfast

theorem sr10p42:∀ i ∈ List.range 1,StrictCheckAt 10 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 42) 10 42:=by decide +kernel
  have hfast:StrictAtFast (row 10 42) 10 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 42) 10 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 42) 10 42 hvalid hfast

theorem sr10p43:∀ i ∈ List.range 1,StrictCheckAt 10 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 43) 10 43:=by decide +kernel
  have hfast:StrictAtFast (row 10 43) 10 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 43) 10 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 43) 10 43 hvalid hfast

theorem sr10p44:∀ i ∈ List.range 1,StrictCheckAt 10 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 44) 10 44:=by decide +kernel
  have hfast:StrictAtFast (row 10 44) 10 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 44) 10 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 44) 10 44 hvalid hfast

theorem sr10p45:∀ i ∈ List.range 1,StrictCheckAt 10 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 45) 10 45:=by decide +kernel
  have hfast:StrictAtFast (row 10 45) 10 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 45) 10 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 45) 10 45 hvalid hfast

theorem sr10p46:∀ i ∈ List.range 1,StrictCheckAt 10 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 46) 10 46:=by decide +kernel
  have hfast:StrictAtFast (row 10 46) 10 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 46) 10 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 46) 10 46 hvalid hfast

theorem sr10p47:∀ i ∈ List.range 1,StrictCheckAt 10 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 47) 10 47:=by decide +kernel
  have hfast:StrictAtFast (row 10 47) 10 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 47) 10 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 47) 10 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
