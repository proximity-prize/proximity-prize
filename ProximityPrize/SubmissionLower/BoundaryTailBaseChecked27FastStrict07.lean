import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr27p96:∀ i ∈ List.range 1,StrictCheckAt 27 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 96) 27 96:=by decide +kernel
  have hfast:StrictAtFast (row 27 96) 27 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 96) 27 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 96) 27 96 hvalid hfast

theorem sr27p97:∀ i ∈ List.range 1,StrictCheckAt 27 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 97) 27 97:=by decide +kernel
  have hfast:StrictAtFast (row 27 97) 27 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 97) 27 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 97) 27 97 hvalid hfast

theorem sr27p98:∀ i ∈ List.range 1,StrictCheckAt 27 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 98) 27 98:=by decide +kernel
  have hfast:StrictAtFast (row 27 98) 27 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 98) 27 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 98) 27 98 hvalid hfast

theorem sr27p99:∀ i ∈ List.range 1,StrictCheckAt 27 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 99) 27 99:=by decide +kernel
  have hfast:StrictAtFast (row 27 99) 27 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 99) 27 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 99) 27 99 hvalid hfast

theorem sr27p100:∀ i ∈ List.range 1,StrictCheckAt 27 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 100) 27 100:=by decide +kernel
  have hfast:StrictAtFast (row 27 100) 27 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 100) 27 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 100) 27 100 hvalid hfast

theorem sr27p101:∀ i ∈ List.range 1,StrictCheckAt 27 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 101) 27 101:=by decide +kernel
  have hfast:StrictAtFast (row 27 101) 27 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 101) 27 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 101) 27 101 hvalid hfast

theorem sr27p102:∀ i ∈ List.range 1,StrictCheckAt 27 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 102) 27 102:=by decide +kernel
  have hfast:StrictAtFast (row 27 102) 27 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 102) 27 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 102) 27 102 hvalid hfast

theorem sr27p103:∀ i ∈ List.range 1,StrictCheckAt 27 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 103) 27 103:=by decide +kernel
  have hfast:StrictAtFast (row 27 103) 27 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 103) 27 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 103) 27 103 hvalid hfast

theorem sr27p104:∀ i ∈ List.range 1,StrictCheckAt 27 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 104) 27 104:=by decide +kernel
  have hfast:StrictAtFast (row 27 104) 27 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 104) 27 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 104) 27 104 hvalid hfast

theorem sr27p105:∀ i ∈ List.range 1,StrictCheckAt 27 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 105) 27 105:=by decide +kernel
  have hfast:StrictAtFast (row 27 105) 27 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 105) 27 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 105) 27 105 hvalid hfast

theorem sr27p106:∀ i ∈ List.range 1,StrictCheckAt 27 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 106) 27 106:=by decide +kernel
  have hfast:StrictAtFast (row 27 106) 27 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 106) 27 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 106) 27 106 hvalid hfast

theorem sr27p107:∀ i ∈ List.range 1,StrictCheckAt 27 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 107) 27 107:=by decide +kernel
  have hfast:StrictAtFast (row 27 107) 27 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 107) 27 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 107) 27 107 hvalid hfast

theorem sr27p108:∀ i ∈ List.range 1,StrictCheckAt 27 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 108) 27 108:=by decide +kernel
  have hfast:StrictAtFast (row 27 108) 27 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 108) 27 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 108) 27 108 hvalid hfast

theorem sr27p109:∀ i ∈ List.range 1,StrictCheckAt 27 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 109) 27 109:=by decide +kernel
  have hfast:StrictAtFast (row 27 109) 27 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 109) 27 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 109) 27 109 hvalid hfast

theorem sr27p110:∀ i ∈ List.range 1,StrictCheckAt 27 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 110) 27 110:=by decide +kernel
  have hfast:StrictAtFast (row 27 110) 27 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 110) 27 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 110) 27 110 hvalid hfast

theorem sr27p111:∀ i ∈ List.range 1,StrictCheckAt 27 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 111) 27 111:=by decide +kernel
  have hfast:StrictAtFast (row 27 111) 27 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 111) 27 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 111) 27 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
