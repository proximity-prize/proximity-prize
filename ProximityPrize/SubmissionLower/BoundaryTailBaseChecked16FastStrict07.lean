import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr16p96:∀ i ∈ List.range 1,StrictCheckAt 16 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 96) 16 96:=by decide +kernel
  have hfast:StrictAtFast (row 16 96) 16 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 96) 16 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 96) 16 96 hvalid hfast

theorem sr16p97:∀ i ∈ List.range 1,StrictCheckAt 16 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 97) 16 97:=by decide +kernel
  have hfast:StrictAtFast (row 16 97) 16 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 97) 16 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 97) 16 97 hvalid hfast

theorem sr16p98:∀ i ∈ List.range 1,StrictCheckAt 16 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 98) 16 98:=by decide +kernel
  have hfast:StrictAtFast (row 16 98) 16 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 98) 16 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 98) 16 98 hvalid hfast

theorem sr16p99:∀ i ∈ List.range 1,StrictCheckAt 16 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 99) 16 99:=by decide +kernel
  have hfast:StrictAtFast (row 16 99) 16 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 99) 16 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 99) 16 99 hvalid hfast

theorem sr16p100:∀ i ∈ List.range 1,StrictCheckAt 16 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 100) 16 100:=by decide +kernel
  have hfast:StrictAtFast (row 16 100) 16 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 100) 16 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 100) 16 100 hvalid hfast

theorem sr16p101:∀ i ∈ List.range 1,StrictCheckAt 16 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 101) 16 101:=by decide +kernel
  have hfast:StrictAtFast (row 16 101) 16 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 101) 16 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 101) 16 101 hvalid hfast

theorem sr16p102:∀ i ∈ List.range 1,StrictCheckAt 16 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 102) 16 102:=by decide +kernel
  have hfast:StrictAtFast (row 16 102) 16 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 102) 16 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 102) 16 102 hvalid hfast

theorem sr16p103:∀ i ∈ List.range 1,StrictCheckAt 16 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 103) 16 103:=by decide +kernel
  have hfast:StrictAtFast (row 16 103) 16 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 103) 16 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 103) 16 103 hvalid hfast

theorem sr16p104:∀ i ∈ List.range 1,StrictCheckAt 16 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 104) 16 104:=by decide +kernel
  have hfast:StrictAtFast (row 16 104) 16 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 104) 16 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 104) 16 104 hvalid hfast

theorem sr16p105:∀ i ∈ List.range 1,StrictCheckAt 16 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 105) 16 105:=by decide +kernel
  have hfast:StrictAtFast (row 16 105) 16 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 105) 16 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 105) 16 105 hvalid hfast

theorem sr16p106:∀ i ∈ List.range 1,StrictCheckAt 16 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 106) 16 106:=by decide +kernel
  have hfast:StrictAtFast (row 16 106) 16 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 106) 16 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 106) 16 106 hvalid hfast

theorem sr16p107:∀ i ∈ List.range 1,StrictCheckAt 16 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 107) 16 107:=by decide +kernel
  have hfast:StrictAtFast (row 16 107) 16 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 107) 16 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 107) 16 107 hvalid hfast

theorem sr16p108:∀ i ∈ List.range 1,StrictCheckAt 16 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 108) 16 108:=by decide +kernel
  have hfast:StrictAtFast (row 16 108) 16 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 108) 16 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 108) 16 108 hvalid hfast

theorem sr16p109:∀ i ∈ List.range 1,StrictCheckAt 16 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 109) 16 109:=by decide +kernel
  have hfast:StrictAtFast (row 16 109) 16 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 109) 16 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 109) 16 109 hvalid hfast

theorem sr16p110:∀ i ∈ List.range 1,StrictCheckAt 16 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 110) 16 110:=by decide +kernel
  have hfast:StrictAtFast (row 16 110) 16 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 110) 16 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 110) 16 110 hvalid hfast

theorem sr16p111:∀ i ∈ List.range 1,StrictCheckAt 16 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 111) 16 111:=by decide +kernel
  have hfast:StrictAtFast (row 16 111) 16 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 111) 16 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 111) 16 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
