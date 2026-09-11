import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr31p96:∀ i ∈ List.range 1,StrictCheckAt 31 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 96) 31 96:=by decide +kernel
  have hfast:StrictAtFast (row 31 96) 31 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 96) 31 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 96) 31 96 hvalid hfast

theorem sr31p97:∀ i ∈ List.range 1,StrictCheckAt 31 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 97) 31 97:=by decide +kernel
  have hfast:StrictAtFast (row 31 97) 31 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 97) 31 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 97) 31 97 hvalid hfast

theorem sr31p98:∀ i ∈ List.range 1,StrictCheckAt 31 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 98) 31 98:=by decide +kernel
  have hfast:StrictAtFast (row 31 98) 31 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 98) 31 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 98) 31 98 hvalid hfast

theorem sr31p99:∀ i ∈ List.range 1,StrictCheckAt 31 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 99) 31 99:=by decide +kernel
  have hfast:StrictAtFast (row 31 99) 31 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 99) 31 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 99) 31 99 hvalid hfast

theorem sr31p100:∀ i ∈ List.range 1,StrictCheckAt 31 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 100) 31 100:=by decide +kernel
  have hfast:StrictAtFast (row 31 100) 31 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 100) 31 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 100) 31 100 hvalid hfast

theorem sr31p101:∀ i ∈ List.range 1,StrictCheckAt 31 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 101) 31 101:=by decide +kernel
  have hfast:StrictAtFast (row 31 101) 31 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 101) 31 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 101) 31 101 hvalid hfast

theorem sr31p102:∀ i ∈ List.range 1,StrictCheckAt 31 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 102) 31 102:=by decide +kernel
  have hfast:StrictAtFast (row 31 102) 31 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 102) 31 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 102) 31 102 hvalid hfast

theorem sr31p103:∀ i ∈ List.range 1,StrictCheckAt 31 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 103) 31 103:=by decide +kernel
  have hfast:StrictAtFast (row 31 103) 31 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 103) 31 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 103) 31 103 hvalid hfast

theorem sr31p104:∀ i ∈ List.range 1,StrictCheckAt 31 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 104) 31 104:=by decide +kernel
  have hfast:StrictAtFast (row 31 104) 31 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 104) 31 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 104) 31 104 hvalid hfast

theorem sr31p105:∀ i ∈ List.range 1,StrictCheckAt 31 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 105) 31 105:=by decide +kernel
  have hfast:StrictAtFast (row 31 105) 31 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 105) 31 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 105) 31 105 hvalid hfast

theorem sr31p106:∀ i ∈ List.range 1,StrictCheckAt 31 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 106) 31 106:=by decide +kernel
  have hfast:StrictAtFast (row 31 106) 31 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 106) 31 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 106) 31 106 hvalid hfast

theorem sr31p107:∀ i ∈ List.range 1,StrictCheckAt 31 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 107) 31 107:=by decide +kernel
  have hfast:StrictAtFast (row 31 107) 31 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 107) 31 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 107) 31 107 hvalid hfast

theorem sr31p108:∀ i ∈ List.range 1,StrictCheckAt 31 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 108) 31 108:=by decide +kernel
  have hfast:StrictAtFast (row 31 108) 31 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 108) 31 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 108) 31 108 hvalid hfast

theorem sr31p109:∀ i ∈ List.range 1,StrictCheckAt 31 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 109) 31 109:=by decide +kernel
  have hfast:StrictAtFast (row 31 109) 31 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 109) 31 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 109) 31 109 hvalid hfast

theorem sr31p110:∀ i ∈ List.range 1,StrictCheckAt 31 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 110) 31 110:=by decide +kernel
  have hfast:StrictAtFast (row 31 110) 31 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 110) 31 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 110) 31 110 hvalid hfast

theorem sr31p111:∀ i ∈ List.range 1,StrictCheckAt 31 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 111) 31 111:=by decide +kernel
  have hfast:StrictAtFast (row 31 111) 31 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 111) 31 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 111) 31 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
