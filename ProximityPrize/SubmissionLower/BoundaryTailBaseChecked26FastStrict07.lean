import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr26p96:∀ i ∈ List.range 1,StrictCheckAt 26 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 96) 26 96:=by decide +kernel
  have hfast:StrictAtFast (row 26 96) 26 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 96) 26 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 96) 26 96 hvalid hfast

theorem sr26p97:∀ i ∈ List.range 1,StrictCheckAt 26 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 97) 26 97:=by decide +kernel
  have hfast:StrictAtFast (row 26 97) 26 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 97) 26 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 97) 26 97 hvalid hfast

theorem sr26p98:∀ i ∈ List.range 1,StrictCheckAt 26 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 98) 26 98:=by decide +kernel
  have hfast:StrictAtFast (row 26 98) 26 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 98) 26 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 98) 26 98 hvalid hfast

theorem sr26p99:∀ i ∈ List.range 1,StrictCheckAt 26 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 99) 26 99:=by decide +kernel
  have hfast:StrictAtFast (row 26 99) 26 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 99) 26 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 99) 26 99 hvalid hfast

theorem sr26p100:∀ i ∈ List.range 1,StrictCheckAt 26 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 100) 26 100:=by decide +kernel
  have hfast:StrictAtFast (row 26 100) 26 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 100) 26 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 100) 26 100 hvalid hfast

theorem sr26p101:∀ i ∈ List.range 1,StrictCheckAt 26 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 101) 26 101:=by decide +kernel
  have hfast:StrictAtFast (row 26 101) 26 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 101) 26 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 101) 26 101 hvalid hfast

theorem sr26p102:∀ i ∈ List.range 1,StrictCheckAt 26 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 102) 26 102:=by decide +kernel
  have hfast:StrictAtFast (row 26 102) 26 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 102) 26 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 102) 26 102 hvalid hfast

theorem sr26p103:∀ i ∈ List.range 1,StrictCheckAt 26 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 103) 26 103:=by decide +kernel
  have hfast:StrictAtFast (row 26 103) 26 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 103) 26 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 103) 26 103 hvalid hfast

theorem sr26p104:∀ i ∈ List.range 1,StrictCheckAt 26 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 104) 26 104:=by decide +kernel
  have hfast:StrictAtFast (row 26 104) 26 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 104) 26 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 104) 26 104 hvalid hfast

theorem sr26p105:∀ i ∈ List.range 1,StrictCheckAt 26 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 105) 26 105:=by decide +kernel
  have hfast:StrictAtFast (row 26 105) 26 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 105) 26 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 105) 26 105 hvalid hfast

theorem sr26p106:∀ i ∈ List.range 1,StrictCheckAt 26 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 106) 26 106:=by decide +kernel
  have hfast:StrictAtFast (row 26 106) 26 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 106) 26 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 106) 26 106 hvalid hfast

theorem sr26p107:∀ i ∈ List.range 1,StrictCheckAt 26 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 107) 26 107:=by decide +kernel
  have hfast:StrictAtFast (row 26 107) 26 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 107) 26 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 107) 26 107 hvalid hfast

theorem sr26p108:∀ i ∈ List.range 1,StrictCheckAt 26 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 108) 26 108:=by decide +kernel
  have hfast:StrictAtFast (row 26 108) 26 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 108) 26 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 108) 26 108 hvalid hfast

theorem sr26p109:∀ i ∈ List.range 1,StrictCheckAt 26 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 109) 26 109:=by decide +kernel
  have hfast:StrictAtFast (row 26 109) 26 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 109) 26 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 109) 26 109 hvalid hfast

theorem sr26p110:∀ i ∈ List.range 1,StrictCheckAt 26 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 110) 26 110:=by decide +kernel
  have hfast:StrictAtFast (row 26 110) 26 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 110) 26 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 110) 26 110 hvalid hfast

theorem sr26p111:∀ i ∈ List.range 1,StrictCheckAt 26 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 111) 26 111:=by decide +kernel
  have hfast:StrictAtFast (row 26 111) 26 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 111) 26 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 111) 26 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
