import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr13p96:∀ i ∈ List.range 1,StrictCheckAt 13 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 96) 13 96:=by decide +kernel
  have hfast:StrictAtFast (row 13 96) 13 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 96) 13 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 96) 13 96 hvalid hfast

theorem sr13p97:∀ i ∈ List.range 1,StrictCheckAt 13 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 97) 13 97:=by decide +kernel
  have hfast:StrictAtFast (row 13 97) 13 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 97) 13 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 97) 13 97 hvalid hfast

theorem sr13p98:∀ i ∈ List.range 1,StrictCheckAt 13 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 98) 13 98:=by decide +kernel
  have hfast:StrictAtFast (row 13 98) 13 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 98) 13 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 98) 13 98 hvalid hfast

theorem sr13p99:∀ i ∈ List.range 1,StrictCheckAt 13 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 99) 13 99:=by decide +kernel
  have hfast:StrictAtFast (row 13 99) 13 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 99) 13 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 99) 13 99 hvalid hfast

theorem sr13p100:∀ i ∈ List.range 1,StrictCheckAt 13 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 100) 13 100:=by decide +kernel
  have hfast:StrictAtFast (row 13 100) 13 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 100) 13 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 100) 13 100 hvalid hfast

theorem sr13p101:∀ i ∈ List.range 1,StrictCheckAt 13 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 101) 13 101:=by decide +kernel
  have hfast:StrictAtFast (row 13 101) 13 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 101) 13 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 101) 13 101 hvalid hfast

theorem sr13p102:∀ i ∈ List.range 1,StrictCheckAt 13 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 102) 13 102:=by decide +kernel
  have hfast:StrictAtFast (row 13 102) 13 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 102) 13 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 102) 13 102 hvalid hfast

theorem sr13p103:∀ i ∈ List.range 1,StrictCheckAt 13 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 103) 13 103:=by decide +kernel
  have hfast:StrictAtFast (row 13 103) 13 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 103) 13 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 103) 13 103 hvalid hfast

theorem sr13p104:∀ i ∈ List.range 1,StrictCheckAt 13 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 104) 13 104:=by decide +kernel
  have hfast:StrictAtFast (row 13 104) 13 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 104) 13 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 104) 13 104 hvalid hfast

theorem sr13p105:∀ i ∈ List.range 1,StrictCheckAt 13 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 105) 13 105:=by decide +kernel
  have hfast:StrictAtFast (row 13 105) 13 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 105) 13 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 105) 13 105 hvalid hfast

theorem sr13p106:∀ i ∈ List.range 1,StrictCheckAt 13 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 106) 13 106:=by decide +kernel
  have hfast:StrictAtFast (row 13 106) 13 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 106) 13 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 106) 13 106 hvalid hfast

theorem sr13p107:∀ i ∈ List.range 1,StrictCheckAt 13 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 107) 13 107:=by decide +kernel
  have hfast:StrictAtFast (row 13 107) 13 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 107) 13 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 107) 13 107 hvalid hfast

theorem sr13p108:∀ i ∈ List.range 1,StrictCheckAt 13 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 108) 13 108:=by decide +kernel
  have hfast:StrictAtFast (row 13 108) 13 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 108) 13 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 108) 13 108 hvalid hfast

theorem sr13p109:∀ i ∈ List.range 1,StrictCheckAt 13 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 109) 13 109:=by decide +kernel
  have hfast:StrictAtFast (row 13 109) 13 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 109) 13 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 109) 13 109 hvalid hfast

theorem sr13p110:∀ i ∈ List.range 1,StrictCheckAt 13 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 110) 13 110:=by decide +kernel
  have hfast:StrictAtFast (row 13 110) 13 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 110) 13 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 110) 13 110 hvalid hfast

theorem sr13p111:∀ i ∈ List.range 1,StrictCheckAt 13 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 111) 13 111:=by decide +kernel
  have hfast:StrictAtFast (row 13 111) 13 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 111) 13 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 111) 13 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
