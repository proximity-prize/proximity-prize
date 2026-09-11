import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr18p96:∀ i ∈ List.range 1,StrictCheckAt 18 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 96) 18 96:=by decide +kernel
  have hfast:StrictAtFast (row 18 96) 18 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 96) 18 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 96) 18 96 hvalid hfast

theorem sr18p97:∀ i ∈ List.range 1,StrictCheckAt 18 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 97) 18 97:=by decide +kernel
  have hfast:StrictAtFast (row 18 97) 18 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 97) 18 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 97) 18 97 hvalid hfast

theorem sr18p98:∀ i ∈ List.range 1,StrictCheckAt 18 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 98) 18 98:=by decide +kernel
  have hfast:StrictAtFast (row 18 98) 18 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 98) 18 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 98) 18 98 hvalid hfast

theorem sr18p99:∀ i ∈ List.range 1,StrictCheckAt 18 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 99) 18 99:=by decide +kernel
  have hfast:StrictAtFast (row 18 99) 18 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 99) 18 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 99) 18 99 hvalid hfast

theorem sr18p100:∀ i ∈ List.range 1,StrictCheckAt 18 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 100) 18 100:=by decide +kernel
  have hfast:StrictAtFast (row 18 100) 18 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 100) 18 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 100) 18 100 hvalid hfast

theorem sr18p101:∀ i ∈ List.range 1,StrictCheckAt 18 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 101) 18 101:=by decide +kernel
  have hfast:StrictAtFast (row 18 101) 18 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 101) 18 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 101) 18 101 hvalid hfast

theorem sr18p102:∀ i ∈ List.range 1,StrictCheckAt 18 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 102) 18 102:=by decide +kernel
  have hfast:StrictAtFast (row 18 102) 18 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 102) 18 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 102) 18 102 hvalid hfast

theorem sr18p103:∀ i ∈ List.range 1,StrictCheckAt 18 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 103) 18 103:=by decide +kernel
  have hfast:StrictAtFast (row 18 103) 18 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 103) 18 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 103) 18 103 hvalid hfast

theorem sr18p104:∀ i ∈ List.range 1,StrictCheckAt 18 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 104) 18 104:=by decide +kernel
  have hfast:StrictAtFast (row 18 104) 18 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 104) 18 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 104) 18 104 hvalid hfast

theorem sr18p105:∀ i ∈ List.range 1,StrictCheckAt 18 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 105) 18 105:=by decide +kernel
  have hfast:StrictAtFast (row 18 105) 18 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 105) 18 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 105) 18 105 hvalid hfast

theorem sr18p106:∀ i ∈ List.range 1,StrictCheckAt 18 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 106) 18 106:=by decide +kernel
  have hfast:StrictAtFast (row 18 106) 18 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 106) 18 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 106) 18 106 hvalid hfast

theorem sr18p107:∀ i ∈ List.range 1,StrictCheckAt 18 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 107) 18 107:=by decide +kernel
  have hfast:StrictAtFast (row 18 107) 18 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 107) 18 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 107) 18 107 hvalid hfast

theorem sr18p108:∀ i ∈ List.range 1,StrictCheckAt 18 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 108) 18 108:=by decide +kernel
  have hfast:StrictAtFast (row 18 108) 18 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 108) 18 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 108) 18 108 hvalid hfast

theorem sr18p109:∀ i ∈ List.range 1,StrictCheckAt 18 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 109) 18 109:=by decide +kernel
  have hfast:StrictAtFast (row 18 109) 18 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 109) 18 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 109) 18 109 hvalid hfast

theorem sr18p110:∀ i ∈ List.range 1,StrictCheckAt 18 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 110) 18 110:=by decide +kernel
  have hfast:StrictAtFast (row 18 110) 18 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 110) 18 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 110) 18 110 hvalid hfast

theorem sr18p111:∀ i ∈ List.range 1,StrictCheckAt 18 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 111) 18 111:=by decide +kernel
  have hfast:StrictAtFast (row 18 111) 18 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 111) 18 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 111) 18 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
