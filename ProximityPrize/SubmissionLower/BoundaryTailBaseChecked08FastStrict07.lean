import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr8p96:∀ i ∈ List.range 1,StrictCheckAt 8 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 96) 8 96:=by decide +kernel
  have hfast:StrictAtFast (row 8 96) 8 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 96) 8 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 96) 8 96 hvalid hfast

theorem sr8p97:∀ i ∈ List.range 1,StrictCheckAt 8 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 97) 8 97:=by decide +kernel
  have hfast:StrictAtFast (row 8 97) 8 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 97) 8 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 97) 8 97 hvalid hfast

theorem sr8p98:∀ i ∈ List.range 1,StrictCheckAt 8 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 98) 8 98:=by decide +kernel
  have hfast:StrictAtFast (row 8 98) 8 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 98) 8 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 98) 8 98 hvalid hfast

theorem sr8p99:∀ i ∈ List.range 1,StrictCheckAt 8 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 99) 8 99:=by decide +kernel
  have hfast:StrictAtFast (row 8 99) 8 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 99) 8 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 99) 8 99 hvalid hfast

theorem sr8p100:∀ i ∈ List.range 1,StrictCheckAt 8 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 100) 8 100:=by decide +kernel
  have hfast:StrictAtFast (row 8 100) 8 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 100) 8 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 100) 8 100 hvalid hfast

theorem sr8p101:∀ i ∈ List.range 1,StrictCheckAt 8 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 101) 8 101:=by decide +kernel
  have hfast:StrictAtFast (row 8 101) 8 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 101) 8 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 101) 8 101 hvalid hfast

theorem sr8p102:∀ i ∈ List.range 1,StrictCheckAt 8 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 102) 8 102:=by decide +kernel
  have hfast:StrictAtFast (row 8 102) 8 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 102) 8 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 102) 8 102 hvalid hfast

theorem sr8p103:∀ i ∈ List.range 1,StrictCheckAt 8 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 103) 8 103:=by decide +kernel
  have hfast:StrictAtFast (row 8 103) 8 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 103) 8 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 103) 8 103 hvalid hfast

theorem sr8p104:∀ i ∈ List.range 1,StrictCheckAt 8 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 104) 8 104:=by decide +kernel
  have hfast:StrictAtFast (row 8 104) 8 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 104) 8 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 104) 8 104 hvalid hfast

theorem sr8p105:∀ i ∈ List.range 1,StrictCheckAt 8 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 105) 8 105:=by decide +kernel
  have hfast:StrictAtFast (row 8 105) 8 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 105) 8 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 105) 8 105 hvalid hfast

theorem sr8p106:∀ i ∈ List.range 1,StrictCheckAt 8 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 106) 8 106:=by decide +kernel
  have hfast:StrictAtFast (row 8 106) 8 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 106) 8 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 106) 8 106 hvalid hfast

theorem sr8p107:∀ i ∈ List.range 1,StrictCheckAt 8 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 107) 8 107:=by decide +kernel
  have hfast:StrictAtFast (row 8 107) 8 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 107) 8 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 107) 8 107 hvalid hfast

theorem sr8p108:∀ i ∈ List.range 1,StrictCheckAt 8 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 108) 8 108:=by decide +kernel
  have hfast:StrictAtFast (row 8 108) 8 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 108) 8 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 108) 8 108 hvalid hfast

theorem sr8p109:∀ i ∈ List.range 1,StrictCheckAt 8 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 109) 8 109:=by decide +kernel
  have hfast:StrictAtFast (row 8 109) 8 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 109) 8 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 109) 8 109 hvalid hfast

theorem sr8p110:∀ i ∈ List.range 1,StrictCheckAt 8 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 110) 8 110:=by decide +kernel
  have hfast:StrictAtFast (row 8 110) 8 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 110) 8 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 110) 8 110 hvalid hfast

theorem sr8p111:∀ i ∈ List.range 1,StrictCheckAt 8 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 111) 8 111:=by decide +kernel
  have hfast:StrictAtFast (row 8 111) 8 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 111) 8 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 111) 8 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
