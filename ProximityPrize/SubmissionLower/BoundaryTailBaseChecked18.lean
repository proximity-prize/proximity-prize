import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr18p0:∀ i ∈ List.range 8,CorrectAt 18 (0+i):=by decide +kernel

theorem cr18p1:∀ i ∈ List.range 8,CorrectAt 18 (8+i):=by decide +kernel

theorem cr18p2:∀ i ∈ List.range 8,CorrectAt 18 (16+i):=by decide +kernel

theorem cr18p3:∀ i ∈ List.range 8,CorrectAt 18 (24+i):=by decide +kernel

theorem cr18p4:∀ i ∈ List.range 8,CorrectAt 18 (32+i):=by decide +kernel

theorem cr18p5:∀ i ∈ List.range 8,CorrectAt 18 (40+i):=by decide +kernel

theorem cr18p6:∀ i ∈ List.range 8,CorrectAt 18 (48+i):=by decide +kernel

theorem cr18p7:∀ i ∈ List.range 8,CorrectAt 18 (56+i):=by decide +kernel

theorem cr18p8:∀ i ∈ List.range 8,CorrectAt 18 (64+i):=by decide +kernel

theorem cr18p9:∀ i ∈ List.range 8,CorrectAt 18 (72+i):=by decide +kernel

theorem cr18p10:∀ i ∈ List.range 8,CorrectAt 18 (80+i):=by decide +kernel

theorem cr18p11:∀ i ∈ List.range 8,CorrectAt 18 (88+i):=by decide +kernel

theorem cr18p12:∀ i ∈ List.range 8,CorrectAt 18 (96+i):=by decide +kernel

theorem cr18p13:∀ i ∈ List.range 8,CorrectAt 18 (104+i):=by decide +kernel

theorem cr18p14:∀ i ∈ List.range 8,CorrectAt 18 (112+i):=by decide +kernel

theorem cr18p15:∀ i ∈ List.range 5,CorrectAt 18 (120+i):=by decide +kernel

theorem sr18p0:∀ i ∈ List.range 1,StrictCheckAt 18 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 0) 18 0:=by decide +kernel
  have hfast:StrictAtFast (row 18 0) 18 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 0) 18 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 0) 18 0 hvalid hfast

theorem sr18p1:∀ i ∈ List.range 1,StrictCheckAt 18 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 1) 18 1:=by decide +kernel
  have hfast:StrictAtFast (row 18 1) 18 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 1) 18 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 1) 18 1 hvalid hfast

theorem sr18p2:∀ i ∈ List.range 1,StrictCheckAt 18 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 2) 18 2:=by decide +kernel
  have hfast:StrictAtFast (row 18 2) 18 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 2) 18 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 2) 18 2 hvalid hfast

theorem sr18p3:∀ i ∈ List.range 1,StrictCheckAt 18 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 3) 18 3:=by decide +kernel
  have hfast:StrictAtFast (row 18 3) 18 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 3) 18 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 3) 18 3 hvalid hfast

theorem sr18p4:∀ i ∈ List.range 1,StrictCheckAt 18 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 4) 18 4:=by decide +kernel
  have hfast:StrictAtFast (row 18 4) 18 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 4) 18 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 4) 18 4 hvalid hfast

theorem sr18p5:∀ i ∈ List.range 1,StrictCheckAt 18 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 5) 18 5:=by decide +kernel
  have hfast:StrictAtFast (row 18 5) 18 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 5) 18 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 5) 18 5 hvalid hfast

theorem sr18p6:∀ i ∈ List.range 1,StrictCheckAt 18 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 6) 18 6:=by decide +kernel
  have hfast:StrictAtFast (row 18 6) 18 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 6) 18 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 6) 18 6 hvalid hfast

theorem sr18p7:∀ i ∈ List.range 1,StrictCheckAt 18 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 7) 18 7:=by decide +kernel
  have hfast:StrictAtFast (row 18 7) 18 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 7) 18 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 7) 18 7 hvalid hfast

theorem sr18p8:∀ i ∈ List.range 1,StrictCheckAt 18 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 8) 18 8:=by decide +kernel
  have hfast:StrictAtFast (row 18 8) 18 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 8) 18 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 8) 18 8 hvalid hfast

theorem sr18p9:∀ i ∈ List.range 1,StrictCheckAt 18 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 9) 18 9:=by decide +kernel
  have hfast:StrictAtFast (row 18 9) 18 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 9) 18 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 9) 18 9 hvalid hfast

theorem sr18p10:∀ i ∈ List.range 1,StrictCheckAt 18 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 10) 18 10:=by decide +kernel
  have hfast:StrictAtFast (row 18 10) 18 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 10) 18 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 10) 18 10 hvalid hfast

theorem sr18p11:∀ i ∈ List.range 1,StrictCheckAt 18 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 11) 18 11:=by decide +kernel
  have hfast:StrictAtFast (row 18 11) 18 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 11) 18 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 11) 18 11 hvalid hfast

theorem sr18p12:∀ i ∈ List.range 1,StrictCheckAt 18 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 12) 18 12:=by decide +kernel
  have hfast:StrictAtFast (row 18 12) 18 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 12) 18 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 12) 18 12 hvalid hfast

theorem sr18p13:∀ i ∈ List.range 1,StrictCheckAt 18 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 13) 18 13:=by decide +kernel
  have hfast:StrictAtFast (row 18 13) 18 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 13) 18 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 13) 18 13 hvalid hfast

theorem sr18p14:∀ i ∈ List.range 1,StrictCheckAt 18 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 14) 18 14:=by decide +kernel
  have hfast:StrictAtFast (row 18 14) 18 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 14) 18 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 14) 18 14 hvalid hfast

theorem sr18p15:∀ i ∈ List.range 1,StrictCheckAt 18 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 15) 18 15:=by decide +kernel
  have hfast:StrictAtFast (row 18 15) 18 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 15) 18 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 15) 18 15 hvalid hfast

theorem sr18p16:∀ i ∈ List.range 1,StrictCheckAt 18 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 16) 18 16:=by decide +kernel
  have hfast:StrictAtFast (row 18 16) 18 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 16) 18 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 16) 18 16 hvalid hfast

theorem sr18p17:∀ i ∈ List.range 1,StrictCheckAt 18 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 17) 18 17:=by decide +kernel
  have hfast:StrictAtFast (row 18 17) 18 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 17) 18 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 17) 18 17 hvalid hfast

theorem sr18p18:∀ i ∈ List.range 1,StrictCheckAt 18 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 18) 18 18:=by decide +kernel
  have hfast:StrictAtFast (row 18 18) 18 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 18) 18 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 18) 18 18 hvalid hfast

theorem sr18p19:∀ i ∈ List.range 1,StrictCheckAt 18 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 19) 18 19:=by decide +kernel
  have hfast:StrictAtFast (row 18 19) 18 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 19) 18 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 19) 18 19 hvalid hfast

theorem sr18p20:∀ i ∈ List.range 1,StrictCheckAt 18 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 20) 18 20:=by decide +kernel
  have hfast:StrictAtFast (row 18 20) 18 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 20) 18 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 20) 18 20 hvalid hfast

theorem sr18p21:∀ i ∈ List.range 1,StrictCheckAt 18 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 21) 18 21:=by decide +kernel
  have hfast:StrictAtFast (row 18 21) 18 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 21) 18 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 21) 18 21 hvalid hfast

theorem sr18p22:∀ i ∈ List.range 1,StrictCheckAt 18 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 22) 18 22:=by decide +kernel
  have hfast:StrictAtFast (row 18 22) 18 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 22) 18 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 22) 18 22 hvalid hfast

theorem sr18p23:∀ i ∈ List.range 1,StrictCheckAt 18 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 23) 18 23:=by decide +kernel
  have hfast:StrictAtFast (row 18 23) 18 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 23) 18 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 23) 18 23 hvalid hfast

theorem sr18p24:∀ i ∈ List.range 1,StrictCheckAt 18 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 24) 18 24:=by decide +kernel
  have hfast:StrictAtFast (row 18 24) 18 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 24) 18 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 24) 18 24 hvalid hfast

theorem sr18p25:∀ i ∈ List.range 1,StrictCheckAt 18 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 25) 18 25:=by decide +kernel
  have hfast:StrictAtFast (row 18 25) 18 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 25) 18 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 25) 18 25 hvalid hfast

theorem sr18p26:∀ i ∈ List.range 1,StrictCheckAt 18 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 26) 18 26:=by decide +kernel
  have hfast:StrictAtFast (row 18 26) 18 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 26) 18 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 26) 18 26 hvalid hfast

theorem sr18p27:∀ i ∈ List.range 1,StrictCheckAt 18 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 27) 18 27:=by decide +kernel
  have hfast:StrictAtFast (row 18 27) 18 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 27) 18 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 27) 18 27 hvalid hfast

theorem sr18p28:∀ i ∈ List.range 1,StrictCheckAt 18 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 28) 18 28:=by decide +kernel
  have hfast:StrictAtFast (row 18 28) 18 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 28) 18 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 28) 18 28 hvalid hfast

theorem sr18p29:∀ i ∈ List.range 1,StrictCheckAt 18 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 29) 18 29:=by decide +kernel
  have hfast:StrictAtFast (row 18 29) 18 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 29) 18 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 29) 18 29 hvalid hfast

theorem sr18p30:∀ i ∈ List.range 1,StrictCheckAt 18 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 30) 18 30:=by decide +kernel
  have hfast:StrictAtFast (row 18 30) 18 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 30) 18 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 30) 18 30 hvalid hfast

theorem sr18p31:∀ i ∈ List.range 1,StrictCheckAt 18 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 31) 18 31:=by decide +kernel
  have hfast:StrictAtFast (row 18 31) 18 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 31) 18 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 31) 18 31 hvalid hfast

theorem sr18p32:∀ i ∈ List.range 1,StrictCheckAt 18 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 32) 18 32:=by decide +kernel
  have hfast:StrictAtFast (row 18 32) 18 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 32) 18 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 32) 18 32 hvalid hfast

theorem sr18p33:∀ i ∈ List.range 1,StrictCheckAt 18 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 33) 18 33:=by decide +kernel
  have hfast:StrictAtFast (row 18 33) 18 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 33) 18 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 33) 18 33 hvalid hfast

theorem sr18p34:∀ i ∈ List.range 1,StrictCheckAt 18 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 34) 18 34:=by decide +kernel
  have hfast:StrictAtFast (row 18 34) 18 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 34) 18 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 34) 18 34 hvalid hfast

theorem sr18p35:∀ i ∈ List.range 1,StrictCheckAt 18 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 35) 18 35:=by decide +kernel
  have hfast:StrictAtFast (row 18 35) 18 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 35) 18 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 35) 18 35 hvalid hfast

theorem sr18p36:∀ i ∈ List.range 1,StrictCheckAt 18 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 36) 18 36:=by decide +kernel
  have hfast:StrictAtFast (row 18 36) 18 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 36) 18 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 36) 18 36 hvalid hfast

theorem sr18p37:∀ i ∈ List.range 1,StrictCheckAt 18 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 37) 18 37:=by decide +kernel
  have hfast:StrictAtFast (row 18 37) 18 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 37) 18 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 37) 18 37 hvalid hfast

theorem sr18p38:∀ i ∈ List.range 1,StrictCheckAt 18 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 38) 18 38:=by decide +kernel
  have hfast:StrictAtFast (row 18 38) 18 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 38) 18 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 38) 18 38 hvalid hfast

theorem sr18p39:∀ i ∈ List.range 1,StrictCheckAt 18 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 39) 18 39:=by decide +kernel
  have hfast:StrictAtFast (row 18 39) 18 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 39) 18 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 39) 18 39 hvalid hfast

theorem sr18p40:∀ i ∈ List.range 1,StrictCheckAt 18 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 40) 18 40:=by decide +kernel
  have hfast:StrictAtFast (row 18 40) 18 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 40) 18 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 40) 18 40 hvalid hfast

theorem sr18p41:∀ i ∈ List.range 1,StrictCheckAt 18 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 41) 18 41:=by decide +kernel
  have hfast:StrictAtFast (row 18 41) 18 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 41) 18 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 41) 18 41 hvalid hfast

theorem sr18p42:∀ i ∈ List.range 1,StrictCheckAt 18 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 42) 18 42:=by decide +kernel
  have hfast:StrictAtFast (row 18 42) 18 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 42) 18 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 42) 18 42 hvalid hfast

theorem sr18p43:∀ i ∈ List.range 1,StrictCheckAt 18 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 43) 18 43:=by decide +kernel
  have hfast:StrictAtFast (row 18 43) 18 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 43) 18 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 43) 18 43 hvalid hfast

theorem sr18p44:∀ i ∈ List.range 1,StrictCheckAt 18 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 44) 18 44:=by decide +kernel
  have hfast:StrictAtFast (row 18 44) 18 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 44) 18 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 44) 18 44 hvalid hfast

theorem sr18p45:∀ i ∈ List.range 1,StrictCheckAt 18 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 45) 18 45:=by decide +kernel
  have hfast:StrictAtFast (row 18 45) 18 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 45) 18 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 45) 18 45 hvalid hfast

theorem sr18p46:∀ i ∈ List.range 1,StrictCheckAt 18 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 46) 18 46:=by decide +kernel
  have hfast:StrictAtFast (row 18 46) 18 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 46) 18 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 46) 18 46 hvalid hfast

theorem sr18p47:∀ i ∈ List.range 1,StrictCheckAt 18 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 47) 18 47:=by decide +kernel
  have hfast:StrictAtFast (row 18 47) 18 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 47) 18 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 47) 18 47 hvalid hfast

theorem sr18p48:∀ i ∈ List.range 1,StrictCheckAt 18 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 48) 18 48:=by decide +kernel
  have hfast:StrictAtFast (row 18 48) 18 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 48) 18 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 48) 18 48 hvalid hfast

theorem sr18p49:∀ i ∈ List.range 1,StrictCheckAt 18 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 49) 18 49:=by decide +kernel
  have hfast:StrictAtFast (row 18 49) 18 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 49) 18 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 49) 18 49 hvalid hfast

theorem sr18p50:∀ i ∈ List.range 1,StrictCheckAt 18 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 50) 18 50:=by decide +kernel
  have hfast:StrictAtFast (row 18 50) 18 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 50) 18 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 50) 18 50 hvalid hfast

theorem sr18p51:∀ i ∈ List.range 1,StrictCheckAt 18 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 51) 18 51:=by decide +kernel
  have hfast:StrictAtFast (row 18 51) 18 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 51) 18 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 51) 18 51 hvalid hfast

theorem sr18p52:∀ i ∈ List.range 1,StrictCheckAt 18 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 52) 18 52:=by decide +kernel
  have hfast:StrictAtFast (row 18 52) 18 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 52) 18 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 52) 18 52 hvalid hfast

theorem sr18p53:∀ i ∈ List.range 1,StrictCheckAt 18 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 53) 18 53:=by decide +kernel
  have hfast:StrictAtFast (row 18 53) 18 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 53) 18 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 53) 18 53 hvalid hfast

theorem sr18p54:∀ i ∈ List.range 1,StrictCheckAt 18 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 54) 18 54:=by decide +kernel
  have hfast:StrictAtFast (row 18 54) 18 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 54) 18 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 54) 18 54 hvalid hfast

theorem sr18p55:∀ i ∈ List.range 1,StrictCheckAt 18 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 55) 18 55:=by decide +kernel
  have hfast:StrictAtFast (row 18 55) 18 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 55) 18 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 55) 18 55 hvalid hfast

theorem sr18p56:∀ i ∈ List.range 1,StrictCheckAt 18 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 56) 18 56:=by decide +kernel
  have hfast:StrictAtFast (row 18 56) 18 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 56) 18 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 56) 18 56 hvalid hfast

theorem sr18p57:∀ i ∈ List.range 1,StrictCheckAt 18 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 57) 18 57:=by decide +kernel
  have hfast:StrictAtFast (row 18 57) 18 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 57) 18 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 57) 18 57 hvalid hfast

theorem sr18p58:∀ i ∈ List.range 1,StrictCheckAt 18 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 58) 18 58:=by decide +kernel
  have hfast:StrictAtFast (row 18 58) 18 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 58) 18 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 58) 18 58 hvalid hfast

theorem sr18p59:∀ i ∈ List.range 1,StrictCheckAt 18 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 59) 18 59:=by decide +kernel
  have hfast:StrictAtFast (row 18 59) 18 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 59) 18 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 59) 18 59 hvalid hfast

theorem sr18p60:∀ i ∈ List.range 1,StrictCheckAt 18 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 60) 18 60:=by decide +kernel
  have hfast:StrictAtFast (row 18 60) 18 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 60) 18 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 60) 18 60 hvalid hfast

theorem sr18p61:∀ i ∈ List.range 1,StrictCheckAt 18 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 61) 18 61:=by decide +kernel
  have hfast:StrictAtFast (row 18 61) 18 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 61) 18 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 61) 18 61 hvalid hfast

theorem sr18p62:∀ i ∈ List.range 1,StrictCheckAt 18 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 62) 18 62:=by decide +kernel
  have hfast:StrictAtFast (row 18 62) 18 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 62) 18 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 62) 18 62 hvalid hfast

theorem sr18p63:∀ i ∈ List.range 1,StrictCheckAt 18 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 63) 18 63:=by decide +kernel
  have hfast:StrictAtFast (row 18 63) 18 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 63) 18 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 63) 18 63 hvalid hfast

theorem sr18p64:∀ i ∈ List.range 1,StrictCheckAt 18 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 64) 18 64:=by decide +kernel
  have hfast:StrictAtFast (row 18 64) 18 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 64) 18 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 64) 18 64 hvalid hfast

theorem sr18p65:∀ i ∈ List.range 1,StrictCheckAt 18 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 65) 18 65:=by decide +kernel
  have hfast:StrictAtFast (row 18 65) 18 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 65) 18 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 65) 18 65 hvalid hfast

theorem sr18p66:∀ i ∈ List.range 1,StrictCheckAt 18 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 66) 18 66:=by decide +kernel
  have hfast:StrictAtFast (row 18 66) 18 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 66) 18 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 66) 18 66 hvalid hfast

theorem sr18p67:∀ i ∈ List.range 1,StrictCheckAt 18 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 67) 18 67:=by decide +kernel
  have hfast:StrictAtFast (row 18 67) 18 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 67) 18 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 67) 18 67 hvalid hfast

theorem sr18p68:∀ i ∈ List.range 1,StrictCheckAt 18 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 68) 18 68:=by decide +kernel
  have hfast:StrictAtFast (row 18 68) 18 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 68) 18 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 68) 18 68 hvalid hfast

theorem sr18p69:∀ i ∈ List.range 1,StrictCheckAt 18 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 69) 18 69:=by decide +kernel
  have hfast:StrictAtFast (row 18 69) 18 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 69) 18 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 69) 18 69 hvalid hfast

theorem sr18p70:∀ i ∈ List.range 1,StrictCheckAt 18 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 70) 18 70:=by decide +kernel
  have hfast:StrictAtFast (row 18 70) 18 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 70) 18 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 70) 18 70 hvalid hfast

theorem sr18p71:∀ i ∈ List.range 1,StrictCheckAt 18 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 71) 18 71:=by decide +kernel
  have hfast:StrictAtFast (row 18 71) 18 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 71) 18 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 71) 18 71 hvalid hfast

theorem sr18p72:∀ i ∈ List.range 1,StrictCheckAt 18 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 72) 18 72:=by decide +kernel
  have hfast:StrictAtFast (row 18 72) 18 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 72) 18 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 72) 18 72 hvalid hfast

theorem sr18p73:∀ i ∈ List.range 1,StrictCheckAt 18 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 73) 18 73:=by decide +kernel
  have hfast:StrictAtFast (row 18 73) 18 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 73) 18 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 73) 18 73 hvalid hfast

theorem sr18p74:∀ i ∈ List.range 1,StrictCheckAt 18 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 74) 18 74:=by decide +kernel
  have hfast:StrictAtFast (row 18 74) 18 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 74) 18 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 74) 18 74 hvalid hfast

theorem sr18p75:∀ i ∈ List.range 1,StrictCheckAt 18 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 75) 18 75:=by decide +kernel
  have hfast:StrictAtFast (row 18 75) 18 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 75) 18 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 75) 18 75 hvalid hfast

theorem sr18p76:∀ i ∈ List.range 1,StrictCheckAt 18 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 76) 18 76:=by decide +kernel
  have hfast:StrictAtFast (row 18 76) 18 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 76) 18 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 76) 18 76 hvalid hfast

theorem sr18p77:∀ i ∈ List.range 1,StrictCheckAt 18 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 77) 18 77:=by decide +kernel
  have hfast:StrictAtFast (row 18 77) 18 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 77) 18 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 77) 18 77 hvalid hfast

theorem sr18p78:∀ i ∈ List.range 1,StrictCheckAt 18 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 78) 18 78:=by decide +kernel
  have hfast:StrictAtFast (row 18 78) 18 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 78) 18 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 78) 18 78 hvalid hfast

theorem sr18p79:∀ i ∈ List.range 1,StrictCheckAt 18 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 79) 18 79:=by decide +kernel
  have hfast:StrictAtFast (row 18 79) 18 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 79) 18 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 79) 18 79 hvalid hfast

theorem sr18p80:∀ i ∈ List.range 1,StrictCheckAt 18 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 80) 18 80:=by decide +kernel
  have hfast:StrictAtFast (row 18 80) 18 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 80) 18 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 80) 18 80 hvalid hfast

theorem sr18p81:∀ i ∈ List.range 1,StrictCheckAt 18 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 81) 18 81:=by decide +kernel
  have hfast:StrictAtFast (row 18 81) 18 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 81) 18 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 81) 18 81 hvalid hfast

theorem sr18p82:∀ i ∈ List.range 1,StrictCheckAt 18 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 82) 18 82:=by decide +kernel
  have hfast:StrictAtFast (row 18 82) 18 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 82) 18 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 82) 18 82 hvalid hfast

theorem sr18p83:∀ i ∈ List.range 1,StrictCheckAt 18 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 83) 18 83:=by decide +kernel
  have hfast:StrictAtFast (row 18 83) 18 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 83) 18 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 83) 18 83 hvalid hfast

theorem sr18p84:∀ i ∈ List.range 1,StrictCheckAt 18 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 84) 18 84:=by decide +kernel
  have hfast:StrictAtFast (row 18 84) 18 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 84) 18 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 84) 18 84 hvalid hfast

theorem sr18p85:∀ i ∈ List.range 1,StrictCheckAt 18 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 85) 18 85:=by decide +kernel
  have hfast:StrictAtFast (row 18 85) 18 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 85) 18 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 85) 18 85 hvalid hfast

theorem sr18p86:∀ i ∈ List.range 1,StrictCheckAt 18 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 86) 18 86:=by decide +kernel
  have hfast:StrictAtFast (row 18 86) 18 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 86) 18 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 86) 18 86 hvalid hfast

theorem sr18p87:∀ i ∈ List.range 1,StrictCheckAt 18 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 87) 18 87:=by decide +kernel
  have hfast:StrictAtFast (row 18 87) 18 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 87) 18 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 87) 18 87 hvalid hfast

theorem sr18p88:∀ i ∈ List.range 1,StrictCheckAt 18 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 88) 18 88:=by decide +kernel
  have hfast:StrictAtFast (row 18 88) 18 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 88) 18 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 88) 18 88 hvalid hfast

theorem sr18p89:∀ i ∈ List.range 1,StrictCheckAt 18 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 89) 18 89:=by decide +kernel
  have hfast:StrictAtFast (row 18 89) 18 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 89) 18 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 89) 18 89 hvalid hfast

theorem sr18p90:∀ i ∈ List.range 1,StrictCheckAt 18 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 90) 18 90:=by decide +kernel
  have hfast:StrictAtFast (row 18 90) 18 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 90) 18 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 90) 18 90 hvalid hfast

theorem sr18p91:∀ i ∈ List.range 1,StrictCheckAt 18 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 91) 18 91:=by decide +kernel
  have hfast:StrictAtFast (row 18 91) 18 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 91) 18 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 91) 18 91 hvalid hfast

theorem sr18p92:∀ i ∈ List.range 1,StrictCheckAt 18 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 92) 18 92:=by decide +kernel
  have hfast:StrictAtFast (row 18 92) 18 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 92) 18 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 92) 18 92 hvalid hfast

theorem sr18p93:∀ i ∈ List.range 1,StrictCheckAt 18 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 93) 18 93:=by decide +kernel
  have hfast:StrictAtFast (row 18 93) 18 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 93) 18 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 93) 18 93 hvalid hfast

theorem sr18p94:∀ i ∈ List.range 1,StrictCheckAt 18 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 94) 18 94:=by decide +kernel
  have hfast:StrictAtFast (row 18 94) 18 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 94) 18 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 94) 18 94 hvalid hfast

theorem sr18p95:∀ i ∈ List.range 1,StrictCheckAt 18 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 95) 18 95:=by decide +kernel
  have hfast:StrictAtFast (row 18 95) 18 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 95) 18 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 95) 18 95 hvalid hfast

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

theorem sr18p112:∀ i ∈ List.range 1,StrictCheckAt 18 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 112) 18 112:=by decide +kernel
  have hfast:StrictAtFast (row 18 112) 18 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 112) 18 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 112) 18 112 hvalid hfast

theorem sr18p113:∀ i ∈ List.range 1,StrictCheckAt 18 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 113) 18 113:=by decide +kernel
  have hfast:StrictAtFast (row 18 113) 18 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 113) 18 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 113) 18 113 hvalid hfast

theorem sr18p114:∀ i ∈ List.range 1,StrictCheckAt 18 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 114) 18 114:=by decide +kernel
  have hfast:StrictAtFast (row 18 114) 18 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 114) 18 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 114) 18 114 hvalid hfast

theorem sr18p115:∀ i ∈ List.range 1,StrictCheckAt 18 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 115) 18 115:=by decide +kernel
  have hfast:StrictAtFast (row 18 115) 18 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 115) 18 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 115) 18 115 hvalid hfast

theorem sr18p116:∀ i ∈ List.range 1,StrictCheckAt 18 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 116) 18 116:=by decide +kernel
  have hfast:StrictAtFast (row 18 116) 18 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 116) 18 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 116) 18 116 hvalid hfast

theorem sr18p117:∀ i ∈ List.range 1,StrictCheckAt 18 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 117) 18 117:=by decide +kernel
  have hfast:StrictAtFast (row 18 117) 18 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 117) 18 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 117) 18 117 hvalid hfast

theorem sr18p118:∀ i ∈ List.range 1,StrictCheckAt 18 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 118) 18 118:=by decide +kernel
  have hfast:StrictAtFast (row 18 118) 18 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 118) 18 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 118) 18 118 hvalid hfast

theorem sr18p119:∀ i ∈ List.range 1,StrictCheckAt 18 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 119) 18 119:=by decide +kernel
  have hfast:StrictAtFast (row 18 119) 18 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 119) 18 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 119) 18 119 hvalid hfast

theorem sr18p120:∀ i ∈ List.range 1,StrictCheckAt 18 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 120) 18 120:=by decide +kernel
  have hfast:StrictAtFast (row 18 120) 18 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 120) 18 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 120) 18 120 hvalid hfast

theorem sr18p121:∀ i ∈ List.range 1,StrictCheckAt 18 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 121) 18 121:=by decide +kernel
  have hfast:StrictAtFast (row 18 121) 18 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 121) 18 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 121) 18 121 hvalid hfast

theorem sr18p122:∀ i ∈ List.range 1,StrictCheckAt 18 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 122) 18 122:=by decide +kernel
  have hfast:StrictAtFast (row 18 122) 18 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 122) 18 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 122) 18 122 hvalid hfast

theorem sr18p123:∀ i ∈ List.range 1,StrictCheckAt 18 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 123) 18 123:=by decide +kernel
  have hfast:StrictAtFast (row 18 123) 18 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 123) 18 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 123) 18 123 hvalid hfast

theorem sr18p124:∀ i ∈ List.range 1,StrictCheckAt 18 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 18 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 18 124) 18 124:=by decide +kernel
  have hfast:StrictAtFast (row 18 124) 18 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 18 124) 18 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 18 124) 18 124 hvalid hfast

theorem br18p0:∀ i ∈ List.range 4,BaseCheckAt 18 (0+i):=by decide +kernel

theorem br18p1:∀ i ∈ List.range 4,BaseCheckAt 18 (4+i):=by decide +kernel

theorem br18p2:∀ i ∈ List.range 4,BaseCheckAt 18 (8+i):=by decide +kernel

theorem br18p3:∀ i ∈ List.range 4,BaseCheckAt 18 (12+i):=by decide +kernel

theorem br18p4:∀ i ∈ List.range 4,BaseCheckAt 18 (16+i):=by decide +kernel

theorem br18p5:∀ i ∈ List.range 4,BaseCheckAt 18 (20+i):=by decide +kernel

theorem br18p6:∀ i ∈ List.range 4,BaseCheckAt 18 (24+i):=by decide +kernel

theorem br18p7:∀ i ∈ List.range 4,BaseCheckAt 18 (28+i):=by decide +kernel

theorem br18p8:∀ i ∈ List.range 4,BaseCheckAt 18 (32+i):=by decide +kernel

theorem br18p9:∀ i ∈ List.range 4,BaseCheckAt 18 (36+i):=by decide +kernel

theorem br18p10:∀ i ∈ List.range 4,BaseCheckAt 18 (40+i):=by decide +kernel

theorem br18p11:∀ i ∈ List.range 4,BaseCheckAt 18 (44+i):=by decide +kernel

theorem br18p12:∀ i ∈ List.range 4,BaseCheckAt 18 (48+i):=by decide +kernel

theorem br18p13:∀ i ∈ List.range 4,BaseCheckAt 18 (52+i):=by decide +kernel

theorem br18p14:∀ i ∈ List.range 4,BaseCheckAt 18 (56+i):=by decide +kernel

theorem br18p15:∀ i ∈ List.range 4,BaseCheckAt 18 (60+i):=by decide +kernel



theorem br18p16:∀ i ∈ List.range 4,BaseCheckAt 18 (64+i):=by decide +kernel

theorem br18p17:∀ i ∈ List.range 4,BaseCheckAt 18 (68+i):=by decide +kernel

theorem br18p18:∀ i ∈ List.range 4,BaseCheckAt 18 (72+i):=by decide +kernel

theorem br18p19:∀ i ∈ List.range 4,BaseCheckAt 18 (76+i):=by decide +kernel

theorem br18p20:∀ i ∈ List.range 4,BaseCheckAt 18 (80+i):=by decide +kernel

theorem br18p21:∀ i ∈ List.range 4,BaseCheckAt 18 (84+i):=by decide +kernel

theorem br18p22:∀ i ∈ List.range 4,BaseCheckAt 18 (88+i):=by decide +kernel

theorem br18p23:∀ i ∈ List.range 4,BaseCheckAt 18 (92+i):=by decide +kernel

theorem br18p24:∀ i ∈ List.range 4,BaseCheckAt 18 (96+i):=by decide +kernel

theorem br18p25:∀ i ∈ List.range 4,BaseCheckAt 18 (100+i):=by decide +kernel

theorem br18p26:∀ i ∈ List.range 4,BaseCheckAt 18 (104+i):=by decide +kernel

theorem br18p27:∀ i ∈ List.range 4,BaseCheckAt 18 (108+i):=by decide +kernel

theorem br18p28:∀ i ∈ List.range 4,BaseCheckAt 18 (112+i):=by decide +kernel

theorem br18p29:∀ i ∈ List.range 4,BaseCheckAt 18 (116+i):=by decide +kernel

theorem br18p30:∀ i ∈ List.range 4,BaseCheckAt 18 (120+i):=by decide +kernel

theorem br18p31:∀ i ∈ List.range 1,BaseCheckAt 18 (124+i):=by decide +kernel



theorem cr18:∀ V ∈ List.range 125,CorrectAt 18 V:=by
  intro V hV
  have hv:V < 125:=List.mem_range.mp hV
  by_cases h0_16:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr18p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr18p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr18p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr18p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr18p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr18p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr18p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr18p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_16:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr18p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr18p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr18p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr18p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_16:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr18p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr18p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_16:V < 120
        · have h:=cr18p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · have h:=cr18p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem zr18:∀ V ∈ List.range 125,ZeroCheckAt 18 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 18 V (by omega) (by omega) (by omega)
theorem sr18:∀ V ∈ List.range 125,StrictCheckAt 18 V:=by
  intro V hV
  have hv:V < 125:=List.mem_range.mp hV
  by_cases h0_125:V < 62
  · by_cases h0_62:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr18p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr18p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr18p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr18p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr18p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr18p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr18p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr18p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr18p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr18p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr18p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr18p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr18p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr18p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr18p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have h:=sr18p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr18p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
            · by_cases h17_19:V < 18
              · have h:=sr18p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr18p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have h:=sr18p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr18p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
            · by_cases h21_23:V < 22
              · have h:=sr18p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr18p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have h:=sr18p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr18p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
            · by_cases h25_27:V < 26
              · have h:=sr18p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr18p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have h:=sr18p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr18p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr18p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr18p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
    · by_cases h31_62:V < 46
      · by_cases h31_46:V < 38
        · by_cases h31_38:V < 34
          · by_cases h31_34:V < 32
            · have h:=sr18p31 (V-31) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
            · by_cases h32_34:V < 33
              · have h:=sr18p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr18p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have h:=sr18p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr18p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
            · by_cases h36_38:V < 37
              · have h:=sr18p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr18p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
        · by_cases h38_46:V < 42
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have h:=sr18p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr18p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
            · by_cases h40_42:V < 41
              · have h:=sr18p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr18p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have h:=sr18p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr18p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
            · by_cases h44_46:V < 45
              · have h:=sr18p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr18p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
      · by_cases h46_62:V < 54
        · by_cases h46_54:V < 50
          · by_cases h46_50:V < 48
            · by_cases h46_48:V < 47
              · have h:=sr18p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr18p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
            · by_cases h48_50:V < 49
              · have h:=sr18p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr18p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have h:=sr18p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr18p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
            · by_cases h52_54:V < 53
              · have h:=sr18p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr18p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
        · by_cases h54_62:V < 58
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have h:=sr18p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr18p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
            · by_cases h56_58:V < 57
              · have h:=sr18p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr18p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
          · by_cases h58_62:V < 60
            · by_cases h58_60:V < 59
              · have h:=sr18p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr18p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
            · by_cases h60_62:V < 61
              · have h:=sr18p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr18p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
  · by_cases h62_125:V < 93
    · by_cases h62_93:V < 77
      · by_cases h62_77:V < 69
        · by_cases h62_69:V < 65
          · by_cases h62_65:V < 63
            · have h:=sr18p62 (V-62) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
            · by_cases h63_65:V < 64
              · have h:=sr18p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr18p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · by_cases h65_69:V < 67
            · by_cases h65_67:V < 66
              · have h:=sr18p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr18p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
            · by_cases h67_69:V < 68
              · have h:=sr18p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr18p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h69_77:V < 73
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have h:=sr18p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr18p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
            · by_cases h71_73:V < 72
              · have h:=sr18p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr18p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have h:=sr18p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr18p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
            · by_cases h75_77:V < 76
              · have h:=sr18p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr18p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h77_93:V < 85
        · by_cases h77_85:V < 81
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have h:=sr18p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr18p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
            · by_cases h79_81:V < 80
              · have h:=sr18p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr18p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have h:=sr18p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr18p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
            · by_cases h83_85:V < 84
              · have h:=sr18p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr18p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h85_93:V < 89
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have h:=sr18p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr18p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
            · by_cases h87_89:V < 88
              · have h:=sr18p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr18p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have h:=sr18p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr18p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr18p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr18p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h93_125:V < 109
      · by_cases h93_109:V < 101
        · by_cases h93_101:V < 97
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have h:=sr18p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr18p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
            · by_cases h95_97:V < 96
              · have h:=sr18p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr18p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have h:=sr18p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr18p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_101:V < 100
              · have h:=sr18p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr18p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h101_109:V < 105
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have h:=sr18p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr18p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr18p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr18p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have h:=sr18p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr18p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
            · by_cases h107_109:V < 108
              · have h:=sr18p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr18p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h109_125:V < 117
        · by_cases h109_117:V < 113
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have h:=sr18p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr18p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
            · by_cases h111_113:V < 112
              · have h:=sr18p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr18p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have h:=sr18p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr18p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
            · by_cases h115_117:V < 116
              · have h:=sr18p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr18p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h117_125:V < 121
          · by_cases h117_121:V < 119
            · by_cases h117_119:V < 118
              · have h:=sr18p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
              · have h:=sr18p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
            · by_cases h119_121:V < 120
              · have h:=sr18p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
              · have h:=sr18p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · by_cases h121_125:V < 123
            · by_cases h121_123:V < 122
              · have h:=sr18p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
              · have h:=sr18p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
            · by_cases h123_125:V < 124
              · have h:=sr18p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
              · have h:=sr18p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h

theorem br18:∀ V ∈ List.range 125,BaseCheckAt 18 V:=by
  intro V hV
  have hv:V < 125:=List.mem_range.mp hV
  by_cases h0_32:V < 64
  · by_cases h0_16:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br18p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br18p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br18p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br18p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br18p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br18p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br18p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br18p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_16:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br18p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br18p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br18p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br18p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_16:V < 56
        · by_cases h12_14:V < 52
          · have h:=br18p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br18p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_16:V < 60
          · have h:=br18p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · have h:=br18p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h16_32:V < 96
    · by_cases h16_24:V < 80
      · by_cases h16_20:V < 72
        · by_cases h16_18:V < 68
          · have h:=br18p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br18p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h18_20:V < 76
          · have h:=br18p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br18p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h20_24:V < 88
        · by_cases h20_22:V < 84
          · have h:=br18p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br18p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br18p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br18p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h24_32:V < 112
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br18p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br18p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br18p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br18p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h28_32:V < 120
        · by_cases h28_30:V < 116
          · have h:=br18p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br18p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h30_32:V < 124
          · have h:=br18p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=br18p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
