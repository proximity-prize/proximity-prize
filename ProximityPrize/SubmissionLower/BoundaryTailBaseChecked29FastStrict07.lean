import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr29p96:∀ i ∈ List.range 1,StrictCheckAt 29 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 96) 29 96:=by decide +kernel
  have hfast:StrictAtFast (row 29 96) 29 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 96) 29 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 96) 29 96 hvalid hfast

theorem sr29p97:∀ i ∈ List.range 1,StrictCheckAt 29 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 97) 29 97:=by decide +kernel
  have hfast:StrictAtFast (row 29 97) 29 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 97) 29 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 97) 29 97 hvalid hfast

theorem sr29p98:∀ i ∈ List.range 1,StrictCheckAt 29 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 98) 29 98:=by decide +kernel
  have hfast:StrictAtFast (row 29 98) 29 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 98) 29 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 98) 29 98 hvalid hfast

theorem sr29p99:∀ i ∈ List.range 1,StrictCheckAt 29 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 99) 29 99:=by decide +kernel
  have hfast:StrictAtFast (row 29 99) 29 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 99) 29 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 99) 29 99 hvalid hfast

theorem sr29p100:∀ i ∈ List.range 1,StrictCheckAt 29 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 100) 29 100:=by decide +kernel
  have hfast:StrictAtFast (row 29 100) 29 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 100) 29 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 100) 29 100 hvalid hfast

theorem sr29p101:∀ i ∈ List.range 1,StrictCheckAt 29 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 101) 29 101:=by decide +kernel
  have hfast:StrictAtFast (row 29 101) 29 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 101) 29 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 101) 29 101 hvalid hfast

theorem sr29p102:∀ i ∈ List.range 1,StrictCheckAt 29 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 102) 29 102:=by decide +kernel
  have hfast:StrictAtFast (row 29 102) 29 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 102) 29 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 102) 29 102 hvalid hfast

theorem sr29p103:∀ i ∈ List.range 1,StrictCheckAt 29 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 103) 29 103:=by decide +kernel
  have hfast:StrictAtFast (row 29 103) 29 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 103) 29 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 103) 29 103 hvalid hfast

theorem sr29p104:∀ i ∈ List.range 1,StrictCheckAt 29 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 104) 29 104:=by decide +kernel
  have hfast:StrictAtFast (row 29 104) 29 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 104) 29 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 104) 29 104 hvalid hfast

theorem sr29p105:∀ i ∈ List.range 1,StrictCheckAt 29 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 105) 29 105:=by decide +kernel
  have hfast:StrictAtFast (row 29 105) 29 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 105) 29 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 105) 29 105 hvalid hfast

theorem sr29p106:∀ i ∈ List.range 1,StrictCheckAt 29 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 106) 29 106:=by decide +kernel
  have hfast:StrictAtFast (row 29 106) 29 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 106) 29 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 106) 29 106 hvalid hfast

theorem sr29p107:∀ i ∈ List.range 1,StrictCheckAt 29 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 107) 29 107:=by decide +kernel
  have hfast:StrictAtFast (row 29 107) 29 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 107) 29 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 107) 29 107 hvalid hfast

theorem sr29p108:∀ i ∈ List.range 1,StrictCheckAt 29 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 108) 29 108:=by decide +kernel
  have hfast:StrictAtFast (row 29 108) 29 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 108) 29 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 108) 29 108 hvalid hfast

theorem sr29p109:∀ i ∈ List.range 1,StrictCheckAt 29 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 109) 29 109:=by decide +kernel
  have hfast:StrictAtFast (row 29 109) 29 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 109) 29 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 109) 29 109 hvalid hfast

theorem sr29p110:∀ i ∈ List.range 1,StrictCheckAt 29 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 110) 29 110:=by decide +kernel
  have hfast:StrictAtFast (row 29 110) 29 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 110) 29 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 110) 29 110 hvalid hfast

theorem sr29p111:∀ i ∈ List.range 1,StrictCheckAt 29 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 111) 29 111:=by decide +kernel
  have hfast:StrictAtFast (row 29 111) 29 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 111) 29 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 111) 29 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
