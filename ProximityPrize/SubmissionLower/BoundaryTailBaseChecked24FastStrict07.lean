import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr24p96:∀ i ∈ List.range 1,StrictCheckAt 24 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 96) 24 96:=by decide +kernel
  have hfast:StrictAtFast (row 24 96) 24 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 96) 24 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 96) 24 96 hvalid hfast

theorem sr24p97:∀ i ∈ List.range 1,StrictCheckAt 24 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 97) 24 97:=by decide +kernel
  have hfast:StrictAtFast (row 24 97) 24 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 97) 24 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 97) 24 97 hvalid hfast

theorem sr24p98:∀ i ∈ List.range 1,StrictCheckAt 24 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 98) 24 98:=by decide +kernel
  have hfast:StrictAtFast (row 24 98) 24 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 98) 24 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 98) 24 98 hvalid hfast

theorem sr24p99:∀ i ∈ List.range 1,StrictCheckAt 24 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 99) 24 99:=by decide +kernel
  have hfast:StrictAtFast (row 24 99) 24 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 99) 24 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 99) 24 99 hvalid hfast

theorem sr24p100:∀ i ∈ List.range 1,StrictCheckAt 24 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 100) 24 100:=by decide +kernel
  have hfast:StrictAtFast (row 24 100) 24 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 100) 24 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 100) 24 100 hvalid hfast

theorem sr24p101:∀ i ∈ List.range 1,StrictCheckAt 24 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 101) 24 101:=by decide +kernel
  have hfast:StrictAtFast (row 24 101) 24 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 101) 24 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 101) 24 101 hvalid hfast

theorem sr24p102:∀ i ∈ List.range 1,StrictCheckAt 24 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 102) 24 102:=by decide +kernel
  have hfast:StrictAtFast (row 24 102) 24 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 102) 24 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 102) 24 102 hvalid hfast

theorem sr24p103:∀ i ∈ List.range 1,StrictCheckAt 24 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 103) 24 103:=by decide +kernel
  have hfast:StrictAtFast (row 24 103) 24 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 103) 24 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 103) 24 103 hvalid hfast

theorem sr24p104:∀ i ∈ List.range 1,StrictCheckAt 24 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 104) 24 104:=by decide +kernel
  have hfast:StrictAtFast (row 24 104) 24 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 104) 24 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 104) 24 104 hvalid hfast

theorem sr24p105:∀ i ∈ List.range 1,StrictCheckAt 24 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 105) 24 105:=by decide +kernel
  have hfast:StrictAtFast (row 24 105) 24 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 105) 24 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 105) 24 105 hvalid hfast

theorem sr24p106:∀ i ∈ List.range 1,StrictCheckAt 24 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 106) 24 106:=by decide +kernel
  have hfast:StrictAtFast (row 24 106) 24 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 106) 24 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 106) 24 106 hvalid hfast

theorem sr24p107:∀ i ∈ List.range 1,StrictCheckAt 24 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 107) 24 107:=by decide +kernel
  have hfast:StrictAtFast (row 24 107) 24 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 107) 24 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 107) 24 107 hvalid hfast

theorem sr24p108:∀ i ∈ List.range 1,StrictCheckAt 24 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 108) 24 108:=by decide +kernel
  have hfast:StrictAtFast (row 24 108) 24 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 108) 24 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 108) 24 108 hvalid hfast

theorem sr24p109:∀ i ∈ List.range 1,StrictCheckAt 24 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 109) 24 109:=by decide +kernel
  have hfast:StrictAtFast (row 24 109) 24 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 109) 24 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 109) 24 109 hvalid hfast

theorem sr24p110:∀ i ∈ List.range 1,StrictCheckAt 24 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 110) 24 110:=by decide +kernel
  have hfast:StrictAtFast (row 24 110) 24 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 110) 24 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 110) 24 110 hvalid hfast

theorem sr24p111:∀ i ∈ List.range 1,StrictCheckAt 24 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 111) 24 111:=by decide +kernel
  have hfast:StrictAtFast (row 24 111) 24 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 111) 24 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 111) 24 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
