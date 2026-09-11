import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr19p96:∀ i ∈ List.range 1,StrictCheckAt 19 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 96) 19 96:=by decide +kernel
  have hfast:StrictAtFast (row 19 96) 19 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 96) 19 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 96) 19 96 hvalid hfast

theorem sr19p97:∀ i ∈ List.range 1,StrictCheckAt 19 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 97) 19 97:=by decide +kernel
  have hfast:StrictAtFast (row 19 97) 19 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 97) 19 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 97) 19 97 hvalid hfast

theorem sr19p98:∀ i ∈ List.range 1,StrictCheckAt 19 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 98) 19 98:=by decide +kernel
  have hfast:StrictAtFast (row 19 98) 19 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 98) 19 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 98) 19 98 hvalid hfast

theorem sr19p99:∀ i ∈ List.range 1,StrictCheckAt 19 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 99) 19 99:=by decide +kernel
  have hfast:StrictAtFast (row 19 99) 19 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 99) 19 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 99) 19 99 hvalid hfast

theorem sr19p100:∀ i ∈ List.range 1,StrictCheckAt 19 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 100) 19 100:=by decide +kernel
  have hfast:StrictAtFast (row 19 100) 19 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 100) 19 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 100) 19 100 hvalid hfast

theorem sr19p101:∀ i ∈ List.range 1,StrictCheckAt 19 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 101) 19 101:=by decide +kernel
  have hfast:StrictAtFast (row 19 101) 19 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 101) 19 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 101) 19 101 hvalid hfast

theorem sr19p102:∀ i ∈ List.range 1,StrictCheckAt 19 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 102) 19 102:=by decide +kernel
  have hfast:StrictAtFast (row 19 102) 19 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 102) 19 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 102) 19 102 hvalid hfast

theorem sr19p103:∀ i ∈ List.range 1,StrictCheckAt 19 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 103) 19 103:=by decide +kernel
  have hfast:StrictAtFast (row 19 103) 19 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 103) 19 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 103) 19 103 hvalid hfast

theorem sr19p104:∀ i ∈ List.range 1,StrictCheckAt 19 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 104) 19 104:=by decide +kernel
  have hfast:StrictAtFast (row 19 104) 19 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 104) 19 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 104) 19 104 hvalid hfast

theorem sr19p105:∀ i ∈ List.range 1,StrictCheckAt 19 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 105) 19 105:=by decide +kernel
  have hfast:StrictAtFast (row 19 105) 19 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 105) 19 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 105) 19 105 hvalid hfast

theorem sr19p106:∀ i ∈ List.range 1,StrictCheckAt 19 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 106) 19 106:=by decide +kernel
  have hfast:StrictAtFast (row 19 106) 19 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 106) 19 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 106) 19 106 hvalid hfast

theorem sr19p107:∀ i ∈ List.range 1,StrictCheckAt 19 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 107) 19 107:=by decide +kernel
  have hfast:StrictAtFast (row 19 107) 19 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 107) 19 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 107) 19 107 hvalid hfast

theorem sr19p108:∀ i ∈ List.range 1,StrictCheckAt 19 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 108) 19 108:=by decide +kernel
  have hfast:StrictAtFast (row 19 108) 19 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 108) 19 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 108) 19 108 hvalid hfast

theorem sr19p109:∀ i ∈ List.range 1,StrictCheckAt 19 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 109) 19 109:=by decide +kernel
  have hfast:StrictAtFast (row 19 109) 19 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 109) 19 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 109) 19 109 hvalid hfast

theorem sr19p110:∀ i ∈ List.range 1,StrictCheckAt 19 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 110) 19 110:=by decide +kernel
  have hfast:StrictAtFast (row 19 110) 19 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 110) 19 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 110) 19 110 hvalid hfast

theorem sr19p111:∀ i ∈ List.range 1,StrictCheckAt 19 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 111) 19 111:=by decide +kernel
  have hfast:StrictAtFast (row 19 111) 19 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 111) 19 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 111) 19 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
