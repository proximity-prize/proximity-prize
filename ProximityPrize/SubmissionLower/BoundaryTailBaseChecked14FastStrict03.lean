import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p32:∀ i ∈ List.range 1,StrictCheckAt 14 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 32) 14 32:=by decide +kernel
  have hfast:StrictAtFast (row 14 32) 14 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 32) 14 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 32) 14 32 hvalid hfast

theorem sr14p33:∀ i ∈ List.range 1,StrictCheckAt 14 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 33) 14 33:=by decide +kernel
  have hfast:StrictAtFast (row 14 33) 14 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 33) 14 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 33) 14 33 hvalid hfast

theorem sr14p34:∀ i ∈ List.range 1,StrictCheckAt 14 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 34) 14 34:=by decide +kernel
  have hfast:StrictAtFast (row 14 34) 14 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 34) 14 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 34) 14 34 hvalid hfast

theorem sr14p35:∀ i ∈ List.range 1,StrictCheckAt 14 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 35) 14 35:=by decide +kernel
  have hfast:StrictAtFast (row 14 35) 14 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 35) 14 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 35) 14 35 hvalid hfast

theorem sr14p36:∀ i ∈ List.range 1,StrictCheckAt 14 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 36) 14 36:=by decide +kernel
  have hfast:StrictAtFast (row 14 36) 14 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 36) 14 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 36) 14 36 hvalid hfast

theorem sr14p37:∀ i ∈ List.range 1,StrictCheckAt 14 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 37) 14 37:=by decide +kernel
  have hfast:StrictAtFast (row 14 37) 14 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 37) 14 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 37) 14 37 hvalid hfast

theorem sr14p38:∀ i ∈ List.range 1,StrictCheckAt 14 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 38) 14 38:=by decide +kernel
  have hfast:StrictAtFast (row 14 38) 14 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 38) 14 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 38) 14 38 hvalid hfast

theorem sr14p39:∀ i ∈ List.range 1,StrictCheckAt 14 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 39) 14 39:=by decide +kernel
  have hfast:StrictAtFast (row 14 39) 14 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 39) 14 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 39) 14 39 hvalid hfast

theorem sr14p40:∀ i ∈ List.range 1,StrictCheckAt 14 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 40) 14 40:=by decide +kernel
  have hfast:StrictAtFast (row 14 40) 14 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 40) 14 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 40) 14 40 hvalid hfast

theorem sr14p41:∀ i ∈ List.range 1,StrictCheckAt 14 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 41) 14 41:=by decide +kernel
  have hfast:StrictAtFast (row 14 41) 14 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 41) 14 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 41) 14 41 hvalid hfast

theorem sr14p42:∀ i ∈ List.range 1,StrictCheckAt 14 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 42) 14 42:=by decide +kernel
  have hfast:StrictAtFast (row 14 42) 14 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 42) 14 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 42) 14 42 hvalid hfast

theorem sr14p43:∀ i ∈ List.range 1,StrictCheckAt 14 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 43) 14 43:=by decide +kernel
  have hfast:StrictAtFast (row 14 43) 14 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 43) 14 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 43) 14 43 hvalid hfast

theorem sr14p44:∀ i ∈ List.range 1,StrictCheckAt 14 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 44) 14 44:=by decide +kernel
  have hfast:StrictAtFast (row 14 44) 14 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 44) 14 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 44) 14 44 hvalid hfast

theorem sr14p45:∀ i ∈ List.range 1,StrictCheckAt 14 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 45) 14 45:=by decide +kernel
  have hfast:StrictAtFast (row 14 45) 14 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 45) 14 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 45) 14 45 hvalid hfast

theorem sr14p46:∀ i ∈ List.range 1,StrictCheckAt 14 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 46) 14 46:=by decide +kernel
  have hfast:StrictAtFast (row 14 46) 14 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 46) 14 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 46) 14 46 hvalid hfast

theorem sr14p47:∀ i ∈ List.range 1,StrictCheckAt 14 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 47) 14 47:=by decide +kernel
  have hfast:StrictAtFast (row 14 47) 14 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 47) 14 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 47) 14 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
