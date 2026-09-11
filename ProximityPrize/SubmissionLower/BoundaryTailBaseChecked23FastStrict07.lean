import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr23p96:∀ i ∈ List.range 1,StrictCheckAt 23 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 96) 23 96:=by decide +kernel
  have hfast:StrictAtFast (row 23 96) 23 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 96) 23 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 96) 23 96 hvalid hfast

theorem sr23p97:∀ i ∈ List.range 1,StrictCheckAt 23 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 97) 23 97:=by decide +kernel
  have hfast:StrictAtFast (row 23 97) 23 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 97) 23 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 97) 23 97 hvalid hfast

theorem sr23p98:∀ i ∈ List.range 1,StrictCheckAt 23 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 98) 23 98:=by decide +kernel
  have hfast:StrictAtFast (row 23 98) 23 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 98) 23 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 98) 23 98 hvalid hfast

theorem sr23p99:∀ i ∈ List.range 1,StrictCheckAt 23 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 99) 23 99:=by decide +kernel
  have hfast:StrictAtFast (row 23 99) 23 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 99) 23 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 99) 23 99 hvalid hfast

theorem sr23p100:∀ i ∈ List.range 1,StrictCheckAt 23 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 100) 23 100:=by decide +kernel
  have hfast:StrictAtFast (row 23 100) 23 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 100) 23 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 100) 23 100 hvalid hfast

theorem sr23p101:∀ i ∈ List.range 1,StrictCheckAt 23 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 101) 23 101:=by decide +kernel
  have hfast:StrictAtFast (row 23 101) 23 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 101) 23 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 101) 23 101 hvalid hfast

theorem sr23p102:∀ i ∈ List.range 1,StrictCheckAt 23 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 102) 23 102:=by decide +kernel
  have hfast:StrictAtFast (row 23 102) 23 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 102) 23 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 102) 23 102 hvalid hfast

theorem sr23p103:∀ i ∈ List.range 1,StrictCheckAt 23 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 103) 23 103:=by decide +kernel
  have hfast:StrictAtFast (row 23 103) 23 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 103) 23 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 103) 23 103 hvalid hfast

theorem sr23p104:∀ i ∈ List.range 1,StrictCheckAt 23 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 104) 23 104:=by decide +kernel
  have hfast:StrictAtFast (row 23 104) 23 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 104) 23 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 104) 23 104 hvalid hfast

theorem sr23p105:∀ i ∈ List.range 1,StrictCheckAt 23 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 105) 23 105:=by decide +kernel
  have hfast:StrictAtFast (row 23 105) 23 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 105) 23 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 105) 23 105 hvalid hfast

theorem sr23p106:∀ i ∈ List.range 1,StrictCheckAt 23 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 106) 23 106:=by decide +kernel
  have hfast:StrictAtFast (row 23 106) 23 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 106) 23 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 106) 23 106 hvalid hfast

theorem sr23p107:∀ i ∈ List.range 1,StrictCheckAt 23 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 107) 23 107:=by decide +kernel
  have hfast:StrictAtFast (row 23 107) 23 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 107) 23 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 107) 23 107 hvalid hfast

theorem sr23p108:∀ i ∈ List.range 1,StrictCheckAt 23 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 108) 23 108:=by decide +kernel
  have hfast:StrictAtFast (row 23 108) 23 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 108) 23 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 108) 23 108 hvalid hfast

theorem sr23p109:∀ i ∈ List.range 1,StrictCheckAt 23 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 109) 23 109:=by decide +kernel
  have hfast:StrictAtFast (row 23 109) 23 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 109) 23 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 109) 23 109 hvalid hfast

theorem sr23p110:∀ i ∈ List.range 1,StrictCheckAt 23 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 110) 23 110:=by decide +kernel
  have hfast:StrictAtFast (row 23 110) 23 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 110) 23 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 110) 23 110 hvalid hfast

theorem sr23p111:∀ i ∈ List.range 1,StrictCheckAt 23 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 111) 23 111:=by decide +kernel
  have hfast:StrictAtFast (row 23 111) 23 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 111) 23 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 111) 23 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
