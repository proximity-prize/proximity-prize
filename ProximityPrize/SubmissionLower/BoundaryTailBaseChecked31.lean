import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr31p0:∀ i ∈ List.range 8,CorrectAt 31 (0+i):=by decide +kernel

theorem cr31p1:∀ i ∈ List.range 8,CorrectAt 31 (8+i):=by decide +kernel

theorem cr31p2:∀ i ∈ List.range 8,CorrectAt 31 (16+i):=by decide +kernel

theorem cr31p3:∀ i ∈ List.range 8,CorrectAt 31 (24+i):=by decide +kernel

theorem cr31p4:∀ i ∈ List.range 8,CorrectAt 31 (32+i):=by decide +kernel

theorem cr31p5:∀ i ∈ List.range 8,CorrectAt 31 (40+i):=by decide +kernel

theorem cr31p6:∀ i ∈ List.range 8,CorrectAt 31 (48+i):=by decide +kernel

theorem cr31p7:∀ i ∈ List.range 8,CorrectAt 31 (56+i):=by decide +kernel

theorem cr31p8:∀ i ∈ List.range 8,CorrectAt 31 (64+i):=by decide +kernel

theorem cr31p9:∀ i ∈ List.range 8,CorrectAt 31 (72+i):=by decide +kernel

theorem cr31p10:∀ i ∈ List.range 8,CorrectAt 31 (80+i):=by decide +kernel

theorem cr31p11:∀ i ∈ List.range 8,CorrectAt 31 (88+i):=by decide +kernel

theorem cr31p12:∀ i ∈ List.range 8,CorrectAt 31 (96+i):=by decide +kernel

theorem cr31p13:∀ i ∈ List.range 8,CorrectAt 31 (104+i):=by decide +kernel

theorem sr31p0:∀ i ∈ List.range 1,StrictCheckAt 31 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 0) 31 0:=by decide +kernel
  have hfast:StrictAtFast (row 31 0) 31 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 0) 31 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 0) 31 0 hvalid hfast

theorem sr31p1:∀ i ∈ List.range 1,StrictCheckAt 31 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 1) 31 1:=by decide +kernel
  have hfast:StrictAtFast (row 31 1) 31 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 1) 31 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 1) 31 1 hvalid hfast

theorem sr31p2:∀ i ∈ List.range 1,StrictCheckAt 31 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 2) 31 2:=by decide +kernel
  have hfast:StrictAtFast (row 31 2) 31 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 2) 31 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 2) 31 2 hvalid hfast

theorem sr31p3:∀ i ∈ List.range 1,StrictCheckAt 31 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 3) 31 3:=by decide +kernel
  have hfast:StrictAtFast (row 31 3) 31 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 3) 31 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 3) 31 3 hvalid hfast

theorem sr31p4:∀ i ∈ List.range 1,StrictCheckAt 31 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 4) 31 4:=by decide +kernel
  have hfast:StrictAtFast (row 31 4) 31 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 4) 31 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 4) 31 4 hvalid hfast

theorem sr31p5:∀ i ∈ List.range 1,StrictCheckAt 31 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 5) 31 5:=by decide +kernel
  have hfast:StrictAtFast (row 31 5) 31 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 5) 31 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 5) 31 5 hvalid hfast

theorem sr31p6:∀ i ∈ List.range 1,StrictCheckAt 31 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 6) 31 6:=by decide +kernel
  have hfast:StrictAtFast (row 31 6) 31 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 6) 31 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 6) 31 6 hvalid hfast

theorem sr31p7:∀ i ∈ List.range 1,StrictCheckAt 31 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 7) 31 7:=by decide +kernel
  have hfast:StrictAtFast (row 31 7) 31 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 7) 31 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 7) 31 7 hvalid hfast

theorem sr31p8:∀ i ∈ List.range 1,StrictCheckAt 31 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 8) 31 8:=by decide +kernel
  have hfast:StrictAtFast (row 31 8) 31 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 8) 31 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 8) 31 8 hvalid hfast

theorem sr31p9:∀ i ∈ List.range 1,StrictCheckAt 31 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 9) 31 9:=by decide +kernel
  have hfast:StrictAtFast (row 31 9) 31 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 9) 31 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 9) 31 9 hvalid hfast

theorem sr31p10:∀ i ∈ List.range 1,StrictCheckAt 31 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 10) 31 10:=by decide +kernel
  have hfast:StrictAtFast (row 31 10) 31 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 10) 31 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 10) 31 10 hvalid hfast

theorem sr31p11:∀ i ∈ List.range 1,StrictCheckAt 31 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 11) 31 11:=by decide +kernel
  have hfast:StrictAtFast (row 31 11) 31 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 11) 31 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 11) 31 11 hvalid hfast

theorem sr31p12:∀ i ∈ List.range 1,StrictCheckAt 31 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 12) 31 12:=by decide +kernel
  have hfast:StrictAtFast (row 31 12) 31 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 12) 31 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 12) 31 12 hvalid hfast

theorem sr31p13:∀ i ∈ List.range 1,StrictCheckAt 31 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 13) 31 13:=by decide +kernel
  have hfast:StrictAtFast (row 31 13) 31 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 13) 31 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 13) 31 13 hvalid hfast

theorem sr31p14:∀ i ∈ List.range 1,StrictCheckAt 31 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 14) 31 14:=by decide +kernel
  have hfast:StrictAtFast (row 31 14) 31 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 14) 31 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 14) 31 14 hvalid hfast

theorem sr31p15:∀ i ∈ List.range 1,StrictCheckAt 31 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 15) 31 15:=by decide +kernel
  have hfast:StrictAtFast (row 31 15) 31 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 15) 31 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 15) 31 15 hvalid hfast

theorem sr31p16:∀ i ∈ List.range 1,StrictCheckAt 31 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 16) 31 16:=by decide +kernel
  have hfast:StrictAtFast (row 31 16) 31 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 16) 31 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 16) 31 16 hvalid hfast

theorem sr31p17:∀ i ∈ List.range 1,StrictCheckAt 31 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 17) 31 17:=by decide +kernel
  have hfast:StrictAtFast (row 31 17) 31 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 17) 31 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 17) 31 17 hvalid hfast

theorem sr31p18:∀ i ∈ List.range 1,StrictCheckAt 31 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 18) 31 18:=by decide +kernel
  have hfast:StrictAtFast (row 31 18) 31 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 18) 31 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 18) 31 18 hvalid hfast

theorem sr31p19:∀ i ∈ List.range 1,StrictCheckAt 31 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 19) 31 19:=by decide +kernel
  have hfast:StrictAtFast (row 31 19) 31 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 19) 31 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 19) 31 19 hvalid hfast

theorem sr31p20:∀ i ∈ List.range 1,StrictCheckAt 31 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 20) 31 20:=by decide +kernel
  have hfast:StrictAtFast (row 31 20) 31 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 20) 31 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 20) 31 20 hvalid hfast

theorem sr31p21:∀ i ∈ List.range 1,StrictCheckAt 31 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 21) 31 21:=by decide +kernel
  have hfast:StrictAtFast (row 31 21) 31 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 21) 31 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 21) 31 21 hvalid hfast

theorem sr31p22:∀ i ∈ List.range 1,StrictCheckAt 31 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 22) 31 22:=by decide +kernel
  have hfast:StrictAtFast (row 31 22) 31 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 22) 31 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 22) 31 22 hvalid hfast

theorem sr31p23:∀ i ∈ List.range 1,StrictCheckAt 31 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 23) 31 23:=by decide +kernel
  have hfast:StrictAtFast (row 31 23) 31 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 23) 31 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 23) 31 23 hvalid hfast

theorem sr31p24:∀ i ∈ List.range 1,StrictCheckAt 31 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 24) 31 24:=by decide +kernel
  have hfast:StrictAtFast (row 31 24) 31 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 24) 31 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 24) 31 24 hvalid hfast

theorem sr31p25:∀ i ∈ List.range 1,StrictCheckAt 31 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 25) 31 25:=by decide +kernel
  have hfast:StrictAtFast (row 31 25) 31 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 25) 31 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 25) 31 25 hvalid hfast

theorem sr31p26:∀ i ∈ List.range 1,StrictCheckAt 31 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 26) 31 26:=by decide +kernel
  have hfast:StrictAtFast (row 31 26) 31 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 26) 31 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 26) 31 26 hvalid hfast

theorem sr31p27:∀ i ∈ List.range 1,StrictCheckAt 31 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 27) 31 27:=by decide +kernel
  have hfast:StrictAtFast (row 31 27) 31 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 27) 31 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 27) 31 27 hvalid hfast

theorem sr31p28:∀ i ∈ List.range 1,StrictCheckAt 31 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 28) 31 28:=by decide +kernel
  have hfast:StrictAtFast (row 31 28) 31 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 28) 31 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 28) 31 28 hvalid hfast

theorem sr31p29:∀ i ∈ List.range 1,StrictCheckAt 31 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 29) 31 29:=by decide +kernel
  have hfast:StrictAtFast (row 31 29) 31 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 29) 31 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 29) 31 29 hvalid hfast

theorem sr31p30:∀ i ∈ List.range 1,StrictCheckAt 31 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 30) 31 30:=by decide +kernel
  have hfast:StrictAtFast (row 31 30) 31 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 30) 31 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 30) 31 30 hvalid hfast

theorem sr31p31:∀ i ∈ List.range 1,StrictCheckAt 31 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 31) 31 31:=by decide +kernel
  have hfast:StrictAtFast (row 31 31) 31 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 31) 31 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 31) 31 31 hvalid hfast

theorem sr31p32:∀ i ∈ List.range 1,StrictCheckAt 31 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 32) 31 32:=by decide +kernel
  have hfast:StrictAtFast (row 31 32) 31 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 32) 31 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 32) 31 32 hvalid hfast

theorem sr31p33:∀ i ∈ List.range 1,StrictCheckAt 31 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 33) 31 33:=by decide +kernel
  have hfast:StrictAtFast (row 31 33) 31 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 33) 31 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 33) 31 33 hvalid hfast

theorem sr31p34:∀ i ∈ List.range 1,StrictCheckAt 31 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 34) 31 34:=by decide +kernel
  have hfast:StrictAtFast (row 31 34) 31 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 34) 31 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 34) 31 34 hvalid hfast

theorem sr31p35:∀ i ∈ List.range 1,StrictCheckAt 31 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 35) 31 35:=by decide +kernel
  have hfast:StrictAtFast (row 31 35) 31 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 35) 31 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 35) 31 35 hvalid hfast

theorem sr31p36:∀ i ∈ List.range 1,StrictCheckAt 31 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 36) 31 36:=by decide +kernel
  have hfast:StrictAtFast (row 31 36) 31 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 36) 31 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 36) 31 36 hvalid hfast

theorem sr31p37:∀ i ∈ List.range 1,StrictCheckAt 31 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 37) 31 37:=by decide +kernel
  have hfast:StrictAtFast (row 31 37) 31 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 37) 31 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 37) 31 37 hvalid hfast

theorem sr31p38:∀ i ∈ List.range 1,StrictCheckAt 31 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 38) 31 38:=by decide +kernel
  have hfast:StrictAtFast (row 31 38) 31 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 38) 31 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 38) 31 38 hvalid hfast

theorem sr31p39:∀ i ∈ List.range 1,StrictCheckAt 31 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 39) 31 39:=by decide +kernel
  have hfast:StrictAtFast (row 31 39) 31 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 39) 31 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 39) 31 39 hvalid hfast

theorem sr31p40:∀ i ∈ List.range 1,StrictCheckAt 31 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 40) 31 40:=by decide +kernel
  have hfast:StrictAtFast (row 31 40) 31 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 40) 31 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 40) 31 40 hvalid hfast

theorem sr31p41:∀ i ∈ List.range 1,StrictCheckAt 31 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 41) 31 41:=by decide +kernel
  have hfast:StrictAtFast (row 31 41) 31 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 41) 31 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 41) 31 41 hvalid hfast

theorem sr31p42:∀ i ∈ List.range 1,StrictCheckAt 31 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 42) 31 42:=by decide +kernel
  have hfast:StrictAtFast (row 31 42) 31 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 42) 31 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 42) 31 42 hvalid hfast

theorem sr31p43:∀ i ∈ List.range 1,StrictCheckAt 31 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 43) 31 43:=by decide +kernel
  have hfast:StrictAtFast (row 31 43) 31 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 43) 31 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 43) 31 43 hvalid hfast

theorem sr31p44:∀ i ∈ List.range 1,StrictCheckAt 31 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 44) 31 44:=by decide +kernel
  have hfast:StrictAtFast (row 31 44) 31 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 44) 31 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 44) 31 44 hvalid hfast

theorem sr31p45:∀ i ∈ List.range 1,StrictCheckAt 31 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 45) 31 45:=by decide +kernel
  have hfast:StrictAtFast (row 31 45) 31 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 45) 31 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 45) 31 45 hvalid hfast

theorem sr31p46:∀ i ∈ List.range 1,StrictCheckAt 31 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 46) 31 46:=by decide +kernel
  have hfast:StrictAtFast (row 31 46) 31 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 46) 31 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 46) 31 46 hvalid hfast

theorem sr31p47:∀ i ∈ List.range 1,StrictCheckAt 31 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 47) 31 47:=by decide +kernel
  have hfast:StrictAtFast (row 31 47) 31 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 47) 31 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 47) 31 47 hvalid hfast

theorem sr31p48:∀ i ∈ List.range 1,StrictCheckAt 31 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 48) 31 48:=by decide +kernel
  have hfast:StrictAtFast (row 31 48) 31 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 48) 31 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 48) 31 48 hvalid hfast

theorem sr31p49:∀ i ∈ List.range 1,StrictCheckAt 31 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 49) 31 49:=by decide +kernel
  have hfast:StrictAtFast (row 31 49) 31 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 49) 31 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 49) 31 49 hvalid hfast

theorem sr31p50:∀ i ∈ List.range 1,StrictCheckAt 31 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 50) 31 50:=by decide +kernel
  have hfast:StrictAtFast (row 31 50) 31 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 50) 31 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 50) 31 50 hvalid hfast

theorem sr31p51:∀ i ∈ List.range 1,StrictCheckAt 31 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 51) 31 51:=by decide +kernel
  have hfast:StrictAtFast (row 31 51) 31 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 51) 31 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 51) 31 51 hvalid hfast

theorem sr31p52:∀ i ∈ List.range 1,StrictCheckAt 31 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 52) 31 52:=by decide +kernel
  have hfast:StrictAtFast (row 31 52) 31 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 52) 31 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 52) 31 52 hvalid hfast

theorem sr31p53:∀ i ∈ List.range 1,StrictCheckAt 31 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 53) 31 53:=by decide +kernel
  have hfast:StrictAtFast (row 31 53) 31 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 53) 31 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 53) 31 53 hvalid hfast

theorem sr31p54:∀ i ∈ List.range 1,StrictCheckAt 31 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 54) 31 54:=by decide +kernel
  have hfast:StrictAtFast (row 31 54) 31 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 54) 31 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 54) 31 54 hvalid hfast

theorem sr31p55:∀ i ∈ List.range 1,StrictCheckAt 31 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 55) 31 55:=by decide +kernel
  have hfast:StrictAtFast (row 31 55) 31 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 55) 31 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 55) 31 55 hvalid hfast

theorem sr31p56:∀ i ∈ List.range 1,StrictCheckAt 31 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 56) 31 56:=by decide +kernel
  have hfast:StrictAtFast (row 31 56) 31 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 56) 31 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 56) 31 56 hvalid hfast

theorem sr31p57:∀ i ∈ List.range 1,StrictCheckAt 31 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 57) 31 57:=by decide +kernel
  have hfast:StrictAtFast (row 31 57) 31 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 57) 31 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 57) 31 57 hvalid hfast

theorem sr31p58:∀ i ∈ List.range 1,StrictCheckAt 31 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 58) 31 58:=by decide +kernel
  have hfast:StrictAtFast (row 31 58) 31 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 58) 31 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 58) 31 58 hvalid hfast

theorem sr31p59:∀ i ∈ List.range 1,StrictCheckAt 31 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 59) 31 59:=by decide +kernel
  have hfast:StrictAtFast (row 31 59) 31 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 59) 31 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 59) 31 59 hvalid hfast

theorem sr31p60:∀ i ∈ List.range 1,StrictCheckAt 31 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 60) 31 60:=by decide +kernel
  have hfast:StrictAtFast (row 31 60) 31 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 60) 31 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 60) 31 60 hvalid hfast

theorem sr31p61:∀ i ∈ List.range 1,StrictCheckAt 31 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 61) 31 61:=by decide +kernel
  have hfast:StrictAtFast (row 31 61) 31 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 61) 31 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 61) 31 61 hvalid hfast

theorem sr31p62:∀ i ∈ List.range 1,StrictCheckAt 31 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 62) 31 62:=by decide +kernel
  have hfast:StrictAtFast (row 31 62) 31 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 62) 31 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 62) 31 62 hvalid hfast

theorem sr31p63:∀ i ∈ List.range 1,StrictCheckAt 31 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 63) 31 63:=by decide +kernel
  have hfast:StrictAtFast (row 31 63) 31 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 63) 31 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 63) 31 63 hvalid hfast

theorem sr31p64:∀ i ∈ List.range 1,StrictCheckAt 31 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 64) 31 64:=by decide +kernel
  have hfast:StrictAtFast (row 31 64) 31 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 64) 31 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 64) 31 64 hvalid hfast

theorem sr31p65:∀ i ∈ List.range 1,StrictCheckAt 31 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 65) 31 65:=by decide +kernel
  have hfast:StrictAtFast (row 31 65) 31 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 65) 31 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 65) 31 65 hvalid hfast

theorem sr31p66:∀ i ∈ List.range 1,StrictCheckAt 31 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 66) 31 66:=by decide +kernel
  have hfast:StrictAtFast (row 31 66) 31 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 66) 31 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 66) 31 66 hvalid hfast

theorem sr31p67:∀ i ∈ List.range 1,StrictCheckAt 31 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 67) 31 67:=by decide +kernel
  have hfast:StrictAtFast (row 31 67) 31 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 67) 31 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 67) 31 67 hvalid hfast

theorem sr31p68:∀ i ∈ List.range 1,StrictCheckAt 31 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 68) 31 68:=by decide +kernel
  have hfast:StrictAtFast (row 31 68) 31 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 68) 31 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 68) 31 68 hvalid hfast

theorem sr31p69:∀ i ∈ List.range 1,StrictCheckAt 31 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 69) 31 69:=by decide +kernel
  have hfast:StrictAtFast (row 31 69) 31 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 69) 31 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 69) 31 69 hvalid hfast

theorem sr31p70:∀ i ∈ List.range 1,StrictCheckAt 31 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 70) 31 70:=by decide +kernel
  have hfast:StrictAtFast (row 31 70) 31 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 70) 31 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 70) 31 70 hvalid hfast

theorem sr31p71:∀ i ∈ List.range 1,StrictCheckAt 31 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 71) 31 71:=by decide +kernel
  have hfast:StrictAtFast (row 31 71) 31 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 71) 31 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 71) 31 71 hvalid hfast

theorem sr31p72:∀ i ∈ List.range 1,StrictCheckAt 31 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 72) 31 72:=by decide +kernel
  have hfast:StrictAtFast (row 31 72) 31 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 72) 31 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 72) 31 72 hvalid hfast

theorem sr31p73:∀ i ∈ List.range 1,StrictCheckAt 31 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 73) 31 73:=by decide +kernel
  have hfast:StrictAtFast (row 31 73) 31 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 73) 31 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 73) 31 73 hvalid hfast

theorem sr31p74:∀ i ∈ List.range 1,StrictCheckAt 31 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 74) 31 74:=by decide +kernel
  have hfast:StrictAtFast (row 31 74) 31 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 74) 31 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 74) 31 74 hvalid hfast

theorem sr31p75:∀ i ∈ List.range 1,StrictCheckAt 31 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 75) 31 75:=by decide +kernel
  have hfast:StrictAtFast (row 31 75) 31 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 75) 31 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 75) 31 75 hvalid hfast

theorem sr31p76:∀ i ∈ List.range 1,StrictCheckAt 31 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 76) 31 76:=by decide +kernel
  have hfast:StrictAtFast (row 31 76) 31 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 76) 31 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 76) 31 76 hvalid hfast

theorem sr31p77:∀ i ∈ List.range 1,StrictCheckAt 31 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 77) 31 77:=by decide +kernel
  have hfast:StrictAtFast (row 31 77) 31 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 77) 31 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 77) 31 77 hvalid hfast

theorem sr31p78:∀ i ∈ List.range 1,StrictCheckAt 31 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 78) 31 78:=by decide +kernel
  have hfast:StrictAtFast (row 31 78) 31 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 78) 31 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 78) 31 78 hvalid hfast

theorem sr31p79:∀ i ∈ List.range 1,StrictCheckAt 31 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 79) 31 79:=by decide +kernel
  have hfast:StrictAtFast (row 31 79) 31 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 79) 31 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 79) 31 79 hvalid hfast

theorem sr31p80:∀ i ∈ List.range 1,StrictCheckAt 31 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 80) 31 80:=by decide +kernel
  have hfast:StrictAtFast (row 31 80) 31 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 80) 31 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 80) 31 80 hvalid hfast

theorem sr31p81:∀ i ∈ List.range 1,StrictCheckAt 31 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 81) 31 81:=by decide +kernel
  have hfast:StrictAtFast (row 31 81) 31 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 81) 31 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 81) 31 81 hvalid hfast

theorem sr31p82:∀ i ∈ List.range 1,StrictCheckAt 31 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 82) 31 82:=by decide +kernel
  have hfast:StrictAtFast (row 31 82) 31 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 82) 31 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 82) 31 82 hvalid hfast

theorem sr31p83:∀ i ∈ List.range 1,StrictCheckAt 31 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 83) 31 83:=by decide +kernel
  have hfast:StrictAtFast (row 31 83) 31 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 83) 31 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 83) 31 83 hvalid hfast

theorem sr31p84:∀ i ∈ List.range 1,StrictCheckAt 31 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 84) 31 84:=by decide +kernel
  have hfast:StrictAtFast (row 31 84) 31 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 84) 31 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 84) 31 84 hvalid hfast

theorem sr31p85:∀ i ∈ List.range 1,StrictCheckAt 31 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 85) 31 85:=by decide +kernel
  have hfast:StrictAtFast (row 31 85) 31 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 85) 31 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 85) 31 85 hvalid hfast

theorem sr31p86:∀ i ∈ List.range 1,StrictCheckAt 31 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 86) 31 86:=by decide +kernel
  have hfast:StrictAtFast (row 31 86) 31 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 86) 31 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 86) 31 86 hvalid hfast

theorem sr31p87:∀ i ∈ List.range 1,StrictCheckAt 31 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 87) 31 87:=by decide +kernel
  have hfast:StrictAtFast (row 31 87) 31 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 87) 31 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 87) 31 87 hvalid hfast

theorem sr31p88:∀ i ∈ List.range 1,StrictCheckAt 31 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 88) 31 88:=by decide +kernel
  have hfast:StrictAtFast (row 31 88) 31 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 88) 31 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 88) 31 88 hvalid hfast

theorem sr31p89:∀ i ∈ List.range 1,StrictCheckAt 31 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 89) 31 89:=by decide +kernel
  have hfast:StrictAtFast (row 31 89) 31 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 89) 31 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 89) 31 89 hvalid hfast

theorem sr31p90:∀ i ∈ List.range 1,StrictCheckAt 31 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 90) 31 90:=by decide +kernel
  have hfast:StrictAtFast (row 31 90) 31 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 90) 31 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 90) 31 90 hvalid hfast

theorem sr31p91:∀ i ∈ List.range 1,StrictCheckAt 31 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 91) 31 91:=by decide +kernel
  have hfast:StrictAtFast (row 31 91) 31 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 91) 31 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 91) 31 91 hvalid hfast

theorem sr31p92:∀ i ∈ List.range 1,StrictCheckAt 31 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 92) 31 92:=by decide +kernel
  have hfast:StrictAtFast (row 31 92) 31 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 92) 31 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 92) 31 92 hvalid hfast

theorem sr31p93:∀ i ∈ List.range 1,StrictCheckAt 31 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 93) 31 93:=by decide +kernel
  have hfast:StrictAtFast (row 31 93) 31 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 93) 31 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 93) 31 93 hvalid hfast

theorem sr31p94:∀ i ∈ List.range 1,StrictCheckAt 31 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 94) 31 94:=by decide +kernel
  have hfast:StrictAtFast (row 31 94) 31 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 94) 31 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 94) 31 94 hvalid hfast

theorem sr31p95:∀ i ∈ List.range 1,StrictCheckAt 31 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 95) 31 95:=by decide +kernel
  have hfast:StrictAtFast (row 31 95) 31 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 95) 31 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 95) 31 95 hvalid hfast

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

theorem br31p0:∀ i ∈ List.range 4,BaseCheckAt 31 (0+i):=by decide +kernel

theorem br31p1:∀ i ∈ List.range 4,BaseCheckAt 31 (4+i):=by decide +kernel

theorem br31p2:∀ i ∈ List.range 4,BaseCheckAt 31 (8+i):=by decide +kernel

theorem br31p3:∀ i ∈ List.range 4,BaseCheckAt 31 (12+i):=by decide +kernel

theorem br31p4:∀ i ∈ List.range 4,BaseCheckAt 31 (16+i):=by decide +kernel

theorem br31p5:∀ i ∈ List.range 4,BaseCheckAt 31 (20+i):=by decide +kernel

theorem br31p6:∀ i ∈ List.range 4,BaseCheckAt 31 (24+i):=by decide +kernel

theorem br31p7:∀ i ∈ List.range 4,BaseCheckAt 31 (28+i):=by decide +kernel

theorem br31p8:∀ i ∈ List.range 4,BaseCheckAt 31 (32+i):=by decide +kernel

theorem br31p9:∀ i ∈ List.range 4,BaseCheckAt 31 (36+i):=by decide +kernel

theorem br31p10:∀ i ∈ List.range 4,BaseCheckAt 31 (40+i):=by decide +kernel

theorem br31p11:∀ i ∈ List.range 4,BaseCheckAt 31 (44+i):=by decide +kernel

theorem br31p12:∀ i ∈ List.range 4,BaseCheckAt 31 (48+i):=by decide +kernel

theorem br31p13:∀ i ∈ List.range 4,BaseCheckAt 31 (52+i):=by decide +kernel

theorem br31p14:∀ i ∈ List.range 4,BaseCheckAt 31 (56+i):=by decide +kernel

theorem br31p15:∀ i ∈ List.range 4,BaseCheckAt 31 (60+i):=by decide +kernel



theorem br31p16:∀ i ∈ List.range 4,BaseCheckAt 31 (64+i):=by decide +kernel

theorem br31p17:∀ i ∈ List.range 4,BaseCheckAt 31 (68+i):=by decide +kernel

theorem br31p18:∀ i ∈ List.range 4,BaseCheckAt 31 (72+i):=by decide +kernel

theorem br31p19:∀ i ∈ List.range 4,BaseCheckAt 31 (76+i):=by decide +kernel

theorem br31p20:∀ i ∈ List.range 4,BaseCheckAt 31 (80+i):=by decide +kernel

theorem br31p21:∀ i ∈ List.range 4,BaseCheckAt 31 (84+i):=by decide +kernel

theorem br31p22:∀ i ∈ List.range 4,BaseCheckAt 31 (88+i):=by decide +kernel

theorem br31p23:∀ i ∈ List.range 4,BaseCheckAt 31 (92+i):=by decide +kernel

theorem br31p24:∀ i ∈ List.range 4,BaseCheckAt 31 (96+i):=by decide +kernel

theorem br31p25:∀ i ∈ List.range 4,BaseCheckAt 31 (100+i):=by decide +kernel

theorem br31p26:∀ i ∈ List.range 4,BaseCheckAt 31 (104+i):=by decide +kernel

theorem br31p27:∀ i ∈ List.range 4,BaseCheckAt 31 (108+i):=by decide +kernel



theorem cr31:∀ V ∈ List.range 112,CorrectAt 31 V:=by
  intro V hV
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0_14:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr31p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr31p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr31p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr31p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr31p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr31p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr31p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_14:V < 80
    · by_cases h7_10:V < 64
      · have h:=cr31p7 (V-56) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
      · by_cases h8_10:V < 72
        · have h:=cr31p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr31p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
    · by_cases h10_14:V < 96
      · by_cases h10_12:V < 88
        · have h:=cr31p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr31p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
      · by_cases h12_14:V < 104
        · have h:=cr31p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr31p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h

theorem zr31:∀ V ∈ List.range 112,ZeroCheckAt 31 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 31 V (by omega) (by omega) (by omega)
theorem sr31:∀ V ∈ List.range 112,StrictCheckAt 31 V:=by
  intro V hV
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0_112:V < 56
  · by_cases h0_56:V < 28
    · by_cases h0_28:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr31p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr31p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr31p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr31p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr31p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr31p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr31p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr31p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr31p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr31p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr31p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr31p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr31p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr31p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_28:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr31p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr31p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr31p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr31p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr31p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr31p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr31p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_28:V < 24
          · by_cases h21_24:V < 22
            · have h:=sr31p21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr31p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr31p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr31p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr31p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr31p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr31p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
    · by_cases h28_56:V < 42
      · by_cases h28_42:V < 35
        · by_cases h28_35:V < 31
          · by_cases h28_31:V < 29
            · have h:=sr31p28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr31p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr31p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have h:=sr31p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr31p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
            · by_cases h33_35:V < 34
              · have h:=sr31p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr31p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
        · by_cases h35_42:V < 38
          · by_cases h35_38:V < 36
            · have h:=sr31p35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
            · by_cases h36_38:V < 37
              · have h:=sr31p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr31p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have h:=sr31p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr31p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
            · by_cases h40_42:V < 41
              · have h:=sr31p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr31p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
      · by_cases h42_56:V < 49
        · by_cases h42_49:V < 45
          · by_cases h42_45:V < 43
            · have h:=sr31p42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr31p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr31p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr31p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr31p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr31p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr31p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h49_56:V < 52
          · by_cases h49_52:V < 50
            · have h:=sr31p49 (V-49) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
            · by_cases h50_52:V < 51
              · have h:=sr31p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr31p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have h:=sr31p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr31p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
            · by_cases h54_56:V < 55
              · have h:=sr31p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr31p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
  · by_cases h56_112:V < 84
    · by_cases h56_84:V < 70
      · by_cases h56_70:V < 63
        · by_cases h56_63:V < 59
          · by_cases h56_59:V < 57
            · have h:=sr31p56 (V-56) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
            · by_cases h57_59:V < 58
              · have h:=sr31p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr31p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have h:=sr31p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr31p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · by_cases h61_63:V < 62
              · have h:=sr31p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr31p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
        · by_cases h63_70:V < 66
          · by_cases h63_66:V < 64
            · have h:=sr31p63 (V-63) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
            · by_cases h64_66:V < 65
              · have h:=sr31p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr31p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have h:=sr31p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr31p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
            · by_cases h68_70:V < 69
              · have h:=sr31p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr31p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
      · by_cases h70_84:V < 77
        · by_cases h70_77:V < 73
          · by_cases h70_73:V < 71
            · have h:=sr31p70 (V-70) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
            · by_cases h71_73:V < 72
              · have h:=sr31p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr31p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have h:=sr31p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr31p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
            · by_cases h75_77:V < 76
              · have h:=sr31p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr31p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
        · by_cases h77_84:V < 80
          · by_cases h77_80:V < 78
            · have h:=sr31p77 (V-77) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
            · by_cases h78_80:V < 79
              · have h:=sr31p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr31p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have h:=sr31p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr31p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
            · by_cases h82_84:V < 83
              · have h:=sr31p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr31p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
    · by_cases h84_112:V < 98
      · by_cases h84_98:V < 91
        · by_cases h84_91:V < 87
          · by_cases h84_87:V < 85
            · have h:=sr31p84 (V-84) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
            · by_cases h85_87:V < 86
              · have h:=sr31p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr31p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have h:=sr31p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr31p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
            · by_cases h89_91:V < 90
              · have h:=sr31p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr31p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
        · by_cases h91_98:V < 94
          · by_cases h91_94:V < 92
            · have h:=sr31p91 (V-91) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr31p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr31p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have h:=sr31p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr31p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
            · by_cases h96_98:V < 97
              · have h:=sr31p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr31p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
      · by_cases h98_112:V < 105
        · by_cases h98_105:V < 101
          · by_cases h98_101:V < 99
            · have h:=sr31p98 (V-98) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_101:V < 100
              · have h:=sr31p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr31p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have h:=sr31p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr31p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr31p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr31p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h105_112:V < 108
          · by_cases h105_108:V < 106
            · have h:=sr31p105 (V-105) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
            · by_cases h106_108:V < 107
              · have h:=sr31p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr31p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have h:=sr31p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr31p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
            · by_cases h110_112:V < 111
              · have h:=sr31p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr31p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h

theorem br31:∀ V ∈ List.range 112,BaseCheckAt 31 V:=by
  intro V hV
  have hv:V < 112:=List.mem_range.mp hV
  by_cases h0_28:V < 56
  · by_cases h0_14:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br31p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br31p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br31p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br31p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br31p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br31p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br31p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_14:V < 40
      · by_cases h7_10:V < 32
        · have h:=br31p7 (V-28) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
        · by_cases h8_10:V < 36
          · have h:=br31p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br31p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
      · by_cases h10_14:V < 48
        · by_cases h10_12:V < 44
          · have h:=br31p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br31p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
        · by_cases h12_14:V < 52
          · have h:=br31p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br31p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
  · by_cases h14_28:V < 84
    · by_cases h14_21:V < 68
      · by_cases h14_17:V < 60
        · have h:=br31p14 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · by_cases h15_17:V < 64
          · have h:=br31p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br31p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br31p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br31p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br31p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br31p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h21_28:V < 96
      · by_cases h21_24:V < 88
        · have h:=br31p21 (V-84) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br31p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br31p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br31p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br31p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br31p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br31p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
