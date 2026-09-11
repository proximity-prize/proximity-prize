import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr11p96:∀ i ∈ List.range 1,StrictCheckAt 11 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 96) 11 96:=by decide +kernel
  have hfast:StrictAtFast (row 11 96) 11 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 96) 11 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 96) 11 96 hvalid hfast

theorem sr11p97:∀ i ∈ List.range 1,StrictCheckAt 11 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 97) 11 97:=by decide +kernel
  have hfast:StrictAtFast (row 11 97) 11 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 97) 11 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 97) 11 97 hvalid hfast

theorem sr11p98:∀ i ∈ List.range 1,StrictCheckAt 11 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 98) 11 98:=by decide +kernel
  have hfast:StrictAtFast (row 11 98) 11 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 98) 11 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 98) 11 98 hvalid hfast

theorem sr11p99:∀ i ∈ List.range 1,StrictCheckAt 11 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 99) 11 99:=by decide +kernel
  have hfast:StrictAtFast (row 11 99) 11 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 99) 11 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 99) 11 99 hvalid hfast

theorem sr11p100:∀ i ∈ List.range 1,StrictCheckAt 11 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 100) 11 100:=by decide +kernel
  have hfast:StrictAtFast (row 11 100) 11 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 100) 11 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 100) 11 100 hvalid hfast

theorem sr11p101:∀ i ∈ List.range 1,StrictCheckAt 11 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 101) 11 101:=by decide +kernel
  have hfast:StrictAtFast (row 11 101) 11 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 101) 11 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 101) 11 101 hvalid hfast

theorem sr11p102:∀ i ∈ List.range 1,StrictCheckAt 11 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 102) 11 102:=by decide +kernel
  have hfast:StrictAtFast (row 11 102) 11 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 102) 11 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 102) 11 102 hvalid hfast

theorem sr11p103:∀ i ∈ List.range 1,StrictCheckAt 11 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 103) 11 103:=by decide +kernel
  have hfast:StrictAtFast (row 11 103) 11 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 103) 11 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 103) 11 103 hvalid hfast

theorem sr11p104:∀ i ∈ List.range 1,StrictCheckAt 11 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 104) 11 104:=by decide +kernel
  have hfast:StrictAtFast (row 11 104) 11 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 104) 11 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 104) 11 104 hvalid hfast

theorem sr11p105:∀ i ∈ List.range 1,StrictCheckAt 11 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 105) 11 105:=by decide +kernel
  have hfast:StrictAtFast (row 11 105) 11 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 105) 11 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 105) 11 105 hvalid hfast

theorem sr11p106:∀ i ∈ List.range 1,StrictCheckAt 11 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 106) 11 106:=by decide +kernel
  have hfast:StrictAtFast (row 11 106) 11 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 106) 11 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 106) 11 106 hvalid hfast

theorem sr11p107:∀ i ∈ List.range 1,StrictCheckAt 11 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 107) 11 107:=by decide +kernel
  have hfast:StrictAtFast (row 11 107) 11 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 107) 11 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 107) 11 107 hvalid hfast

theorem sr11p108:∀ i ∈ List.range 1,StrictCheckAt 11 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 108) 11 108:=by decide +kernel
  have hfast:StrictAtFast (row 11 108) 11 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 108) 11 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 108) 11 108 hvalid hfast

theorem sr11p109:∀ i ∈ List.range 1,StrictCheckAt 11 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 109) 11 109:=by decide +kernel
  have hfast:StrictAtFast (row 11 109) 11 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 109) 11 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 109) 11 109 hvalid hfast

theorem sr11p110:∀ i ∈ List.range 1,StrictCheckAt 11 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 110) 11 110:=by decide +kernel
  have hfast:StrictAtFast (row 11 110) 11 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 110) 11 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 110) 11 110 hvalid hfast

theorem sr11p111:∀ i ∈ List.range 1,StrictCheckAt 11 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 111) 11 111:=by decide +kernel
  have hfast:StrictAtFast (row 11 111) 11 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 111) 11 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 111) 11 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
