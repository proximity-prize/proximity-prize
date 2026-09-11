import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p96:∀ i ∈ List.range 1,StrictCheckAt 14 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 96) 14 96:=by decide +kernel
  have hfast:StrictAtFast (row 14 96) 14 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 96) 14 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 96) 14 96 hvalid hfast

theorem sr14p97:∀ i ∈ List.range 1,StrictCheckAt 14 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 97) 14 97:=by decide +kernel
  have hfast:StrictAtFast (row 14 97) 14 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 97) 14 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 97) 14 97 hvalid hfast

theorem sr14p98:∀ i ∈ List.range 1,StrictCheckAt 14 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 98) 14 98:=by decide +kernel
  have hfast:StrictAtFast (row 14 98) 14 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 98) 14 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 98) 14 98 hvalid hfast

theorem sr14p99:∀ i ∈ List.range 1,StrictCheckAt 14 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 99) 14 99:=by decide +kernel
  have hfast:StrictAtFast (row 14 99) 14 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 99) 14 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 99) 14 99 hvalid hfast

theorem sr14p100:∀ i ∈ List.range 1,StrictCheckAt 14 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 100) 14 100:=by decide +kernel
  have hfast:StrictAtFast (row 14 100) 14 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 100) 14 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 100) 14 100 hvalid hfast

theorem sr14p101:∀ i ∈ List.range 1,StrictCheckAt 14 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 101) 14 101:=by decide +kernel
  have hfast:StrictAtFast (row 14 101) 14 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 101) 14 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 101) 14 101 hvalid hfast

theorem sr14p102:∀ i ∈ List.range 1,StrictCheckAt 14 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 102) 14 102:=by decide +kernel
  have hfast:StrictAtFast (row 14 102) 14 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 102) 14 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 102) 14 102 hvalid hfast

theorem sr14p103:∀ i ∈ List.range 1,StrictCheckAt 14 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 103) 14 103:=by decide +kernel
  have hfast:StrictAtFast (row 14 103) 14 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 103) 14 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 103) 14 103 hvalid hfast

theorem sr14p104:∀ i ∈ List.range 1,StrictCheckAt 14 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 104) 14 104:=by decide +kernel
  have hfast:StrictAtFast (row 14 104) 14 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 104) 14 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 104) 14 104 hvalid hfast

theorem sr14p105:∀ i ∈ List.range 1,StrictCheckAt 14 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 105) 14 105:=by decide +kernel
  have hfast:StrictAtFast (row 14 105) 14 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 105) 14 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 105) 14 105 hvalid hfast

theorem sr14p106:∀ i ∈ List.range 1,StrictCheckAt 14 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 106) 14 106:=by decide +kernel
  have hfast:StrictAtFast (row 14 106) 14 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 106) 14 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 106) 14 106 hvalid hfast

theorem sr14p107:∀ i ∈ List.range 1,StrictCheckAt 14 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 107) 14 107:=by decide +kernel
  have hfast:StrictAtFast (row 14 107) 14 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 107) 14 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 107) 14 107 hvalid hfast

theorem sr14p108:∀ i ∈ List.range 1,StrictCheckAt 14 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 108) 14 108:=by decide +kernel
  have hfast:StrictAtFast (row 14 108) 14 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 108) 14 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 108) 14 108 hvalid hfast

theorem sr14p109:∀ i ∈ List.range 1,StrictCheckAt 14 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 109) 14 109:=by decide +kernel
  have hfast:StrictAtFast (row 14 109) 14 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 109) 14 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 109) 14 109 hvalid hfast

theorem sr14p110:∀ i ∈ List.range 1,StrictCheckAt 14 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 110) 14 110:=by decide +kernel
  have hfast:StrictAtFast (row 14 110) 14 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 110) 14 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 110) 14 110 hvalid hfast

theorem sr14p111:∀ i ∈ List.range 1,StrictCheckAt 14 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 111) 14 111:=by decide +kernel
  have hfast:StrictAtFast (row 14 111) 14 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 111) 14 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 111) 14 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
