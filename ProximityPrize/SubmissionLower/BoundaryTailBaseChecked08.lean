import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr8p0:∀ i ∈ List.range 8,CorrectAt 8 (0+i):=by decide +kernel

theorem cr8p1:∀ i ∈ List.range 8,CorrectAt 8 (8+i):=by decide +kernel

theorem cr8p2:∀ i ∈ List.range 8,CorrectAt 8 (16+i):=by decide +kernel

theorem cr8p3:∀ i ∈ List.range 8,CorrectAt 8 (24+i):=by decide +kernel

theorem cr8p4:∀ i ∈ List.range 8,CorrectAt 8 (32+i):=by decide +kernel

theorem cr8p5:∀ i ∈ List.range 8,CorrectAt 8 (40+i):=by decide +kernel

theorem cr8p6:∀ i ∈ List.range 8,CorrectAt 8 (48+i):=by decide +kernel

theorem cr8p7:∀ i ∈ List.range 8,CorrectAt 8 (56+i):=by decide +kernel

theorem cr8p8:∀ i ∈ List.range 8,CorrectAt 8 (64+i):=by decide +kernel

theorem cr8p9:∀ i ∈ List.range 8,CorrectAt 8 (72+i):=by decide +kernel

theorem cr8p10:∀ i ∈ List.range 8,CorrectAt 8 (80+i):=by decide +kernel

theorem cr8p11:∀ i ∈ List.range 8,CorrectAt 8 (88+i):=by decide +kernel

theorem cr8p12:∀ i ∈ List.range 8,CorrectAt 8 (96+i):=by decide +kernel

theorem cr8p13:∀ i ∈ List.range 8,CorrectAt 8 (104+i):=by decide +kernel

theorem cr8p14:∀ i ∈ List.range 8,CorrectAt 8 (112+i):=by decide +kernel

theorem cr8p15:∀ i ∈ List.range 8,CorrectAt 8 (120+i):=by decide +kernel

theorem cr8p16:∀ i ∈ List.range 7,CorrectAt 8 (128+i):=by decide +kernel

theorem sr8p0:∀ i ∈ List.range 1,StrictCheckAt 8 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 0) 8 0:=by decide +kernel
  have hfast:StrictAtFast (row 8 0) 8 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 0) 8 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 0) 8 0 hvalid hfast

theorem sr8p1:∀ i ∈ List.range 1,StrictCheckAt 8 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 1) 8 1:=by decide +kernel
  have hfast:StrictAtFast (row 8 1) 8 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 1) 8 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 1) 8 1 hvalid hfast

theorem sr8p2:∀ i ∈ List.range 1,StrictCheckAt 8 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 2) 8 2:=by decide +kernel
  have hfast:StrictAtFast (row 8 2) 8 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 2) 8 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 2) 8 2 hvalid hfast

theorem sr8p3:∀ i ∈ List.range 1,StrictCheckAt 8 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 3) 8 3:=by decide +kernel
  have hfast:StrictAtFast (row 8 3) 8 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 3) 8 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 3) 8 3 hvalid hfast

theorem sr8p4:∀ i ∈ List.range 1,StrictCheckAt 8 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 4) 8 4:=by decide +kernel
  have hfast:StrictAtFast (row 8 4) 8 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 4) 8 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 4) 8 4 hvalid hfast

theorem sr8p5:∀ i ∈ List.range 1,StrictCheckAt 8 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 5) 8 5:=by decide +kernel
  have hfast:StrictAtFast (row 8 5) 8 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 5) 8 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 5) 8 5 hvalid hfast

theorem sr8p6:∀ i ∈ List.range 1,StrictCheckAt 8 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 6) 8 6:=by decide +kernel
  have hfast:StrictAtFast (row 8 6) 8 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 6) 8 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 6) 8 6 hvalid hfast

theorem sr8p7:∀ i ∈ List.range 1,StrictCheckAt 8 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 7) 8 7:=by decide +kernel
  have hfast:StrictAtFast (row 8 7) 8 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 7) 8 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 7) 8 7 hvalid hfast

theorem sr8p8:∀ i ∈ List.range 1,StrictCheckAt 8 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 8) 8 8:=by decide +kernel
  have hfast:StrictAtFast (row 8 8) 8 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 8) 8 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 8) 8 8 hvalid hfast

theorem sr8p9:∀ i ∈ List.range 1,StrictCheckAt 8 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 9) 8 9:=by decide +kernel
  have hfast:StrictAtFast (row 8 9) 8 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 9) 8 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 9) 8 9 hvalid hfast

theorem sr8p10:∀ i ∈ List.range 1,StrictCheckAt 8 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 10) 8 10:=by decide +kernel
  have hfast:StrictAtFast (row 8 10) 8 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 10) 8 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 10) 8 10 hvalid hfast

theorem sr8p11:∀ i ∈ List.range 1,StrictCheckAt 8 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 11) 8 11:=by decide +kernel
  have hfast:StrictAtFast (row 8 11) 8 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 11) 8 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 11) 8 11 hvalid hfast

theorem sr8p12:∀ i ∈ List.range 1,StrictCheckAt 8 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 12) 8 12:=by decide +kernel
  have hfast:StrictAtFast (row 8 12) 8 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 12) 8 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 12) 8 12 hvalid hfast

theorem sr8p13:∀ i ∈ List.range 1,StrictCheckAt 8 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 13) 8 13:=by decide +kernel
  have hfast:StrictAtFast (row 8 13) 8 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 13) 8 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 13) 8 13 hvalid hfast

theorem sr8p14:∀ i ∈ List.range 1,StrictCheckAt 8 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 14) 8 14:=by decide +kernel
  have hfast:StrictAtFast (row 8 14) 8 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 14) 8 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 14) 8 14 hvalid hfast

theorem sr8p15:∀ i ∈ List.range 1,StrictCheckAt 8 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 15) 8 15:=by decide +kernel
  have hfast:StrictAtFast (row 8 15) 8 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 15) 8 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 15) 8 15 hvalid hfast

theorem sr8p16:∀ i ∈ List.range 1,StrictCheckAt 8 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 16) 8 16:=by decide +kernel
  have hfast:StrictAtFast (row 8 16) 8 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 16) 8 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 16) 8 16 hvalid hfast

theorem sr8p17:∀ i ∈ List.range 1,StrictCheckAt 8 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 17) 8 17:=by decide +kernel
  have hfast:StrictAtFast (row 8 17) 8 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 17) 8 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 17) 8 17 hvalid hfast

theorem sr8p18:∀ i ∈ List.range 1,StrictCheckAt 8 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 18) 8 18:=by decide +kernel
  have hfast:StrictAtFast (row 8 18) 8 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 18) 8 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 18) 8 18 hvalid hfast

theorem sr8p19:∀ i ∈ List.range 1,StrictCheckAt 8 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 19) 8 19:=by decide +kernel
  have hfast:StrictAtFast (row 8 19) 8 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 19) 8 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 19) 8 19 hvalid hfast

theorem sr8p20:∀ i ∈ List.range 1,StrictCheckAt 8 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 20) 8 20:=by decide +kernel
  have hfast:StrictAtFast (row 8 20) 8 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 20) 8 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 20) 8 20 hvalid hfast

theorem sr8p21:∀ i ∈ List.range 1,StrictCheckAt 8 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 21) 8 21:=by decide +kernel
  have hfast:StrictAtFast (row 8 21) 8 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 21) 8 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 21) 8 21 hvalid hfast

theorem sr8p22:∀ i ∈ List.range 1,StrictCheckAt 8 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 22) 8 22:=by decide +kernel
  have hfast:StrictAtFast (row 8 22) 8 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 22) 8 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 22) 8 22 hvalid hfast

theorem sr8p23:∀ i ∈ List.range 1,StrictCheckAt 8 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 23) 8 23:=by decide +kernel
  have hfast:StrictAtFast (row 8 23) 8 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 23) 8 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 23) 8 23 hvalid hfast

theorem sr8p24:∀ i ∈ List.range 1,StrictCheckAt 8 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 24) 8 24:=by decide +kernel
  have hfast:StrictAtFast (row 8 24) 8 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 24) 8 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 24) 8 24 hvalid hfast

theorem sr8p25:∀ i ∈ List.range 1,StrictCheckAt 8 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 25) 8 25:=by decide +kernel
  have hfast:StrictAtFast (row 8 25) 8 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 25) 8 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 25) 8 25 hvalid hfast

theorem sr8p26:∀ i ∈ List.range 1,StrictCheckAt 8 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 26) 8 26:=by decide +kernel
  have hfast:StrictAtFast (row 8 26) 8 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 26) 8 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 26) 8 26 hvalid hfast

theorem sr8p27:∀ i ∈ List.range 1,StrictCheckAt 8 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 27) 8 27:=by decide +kernel
  have hfast:StrictAtFast (row 8 27) 8 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 27) 8 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 27) 8 27 hvalid hfast

theorem sr8p28:∀ i ∈ List.range 1,StrictCheckAt 8 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 28) 8 28:=by decide +kernel
  have hfast:StrictAtFast (row 8 28) 8 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 28) 8 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 28) 8 28 hvalid hfast

theorem sr8p29:∀ i ∈ List.range 1,StrictCheckAt 8 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 29) 8 29:=by decide +kernel
  have hfast:StrictAtFast (row 8 29) 8 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 29) 8 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 29) 8 29 hvalid hfast

theorem sr8p30:∀ i ∈ List.range 1,StrictCheckAt 8 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 30) 8 30:=by decide +kernel
  have hfast:StrictAtFast (row 8 30) 8 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 30) 8 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 30) 8 30 hvalid hfast

theorem sr8p31:∀ i ∈ List.range 1,StrictCheckAt 8 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 31) 8 31:=by decide +kernel
  have hfast:StrictAtFast (row 8 31) 8 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 31) 8 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 31) 8 31 hvalid hfast

theorem sr8p32:∀ i ∈ List.range 1,StrictCheckAt 8 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 32) 8 32:=by decide +kernel
  have hfast:StrictAtFast (row 8 32) 8 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 32) 8 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 32) 8 32 hvalid hfast

theorem sr8p33:∀ i ∈ List.range 1,StrictCheckAt 8 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 33) 8 33:=by decide +kernel
  have hfast:StrictAtFast (row 8 33) 8 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 33) 8 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 33) 8 33 hvalid hfast

theorem sr8p34:∀ i ∈ List.range 1,StrictCheckAt 8 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 34) 8 34:=by decide +kernel
  have hfast:StrictAtFast (row 8 34) 8 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 34) 8 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 34) 8 34 hvalid hfast

theorem sr8p35:∀ i ∈ List.range 1,StrictCheckAt 8 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 35) 8 35:=by decide +kernel
  have hfast:StrictAtFast (row 8 35) 8 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 35) 8 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 35) 8 35 hvalid hfast

theorem sr8p36:∀ i ∈ List.range 1,StrictCheckAt 8 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 36) 8 36:=by decide +kernel
  have hfast:StrictAtFast (row 8 36) 8 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 36) 8 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 36) 8 36 hvalid hfast

theorem sr8p37:∀ i ∈ List.range 1,StrictCheckAt 8 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 37) 8 37:=by decide +kernel
  have hfast:StrictAtFast (row 8 37) 8 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 37) 8 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 37) 8 37 hvalid hfast

theorem sr8p38:∀ i ∈ List.range 1,StrictCheckAt 8 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 38) 8 38:=by decide +kernel
  have hfast:StrictAtFast (row 8 38) 8 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 38) 8 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 38) 8 38 hvalid hfast

theorem sr8p39:∀ i ∈ List.range 1,StrictCheckAt 8 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 39) 8 39:=by decide +kernel
  have hfast:StrictAtFast (row 8 39) 8 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 39) 8 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 39) 8 39 hvalid hfast

theorem sr8p40:∀ i ∈ List.range 1,StrictCheckAt 8 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 40) 8 40:=by decide +kernel
  have hfast:StrictAtFast (row 8 40) 8 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 40) 8 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 40) 8 40 hvalid hfast

theorem sr8p41:∀ i ∈ List.range 1,StrictCheckAt 8 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 41) 8 41:=by decide +kernel
  have hfast:StrictAtFast (row 8 41) 8 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 41) 8 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 41) 8 41 hvalid hfast

theorem sr8p42:∀ i ∈ List.range 1,StrictCheckAt 8 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 42) 8 42:=by decide +kernel
  have hfast:StrictAtFast (row 8 42) 8 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 42) 8 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 42) 8 42 hvalid hfast

theorem sr8p43:∀ i ∈ List.range 1,StrictCheckAt 8 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 43) 8 43:=by decide +kernel
  have hfast:StrictAtFast (row 8 43) 8 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 43) 8 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 43) 8 43 hvalid hfast

theorem sr8p44:∀ i ∈ List.range 1,StrictCheckAt 8 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 44) 8 44:=by decide +kernel
  have hfast:StrictAtFast (row 8 44) 8 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 44) 8 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 44) 8 44 hvalid hfast

theorem sr8p45:∀ i ∈ List.range 1,StrictCheckAt 8 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 45) 8 45:=by decide +kernel
  have hfast:StrictAtFast (row 8 45) 8 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 45) 8 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 45) 8 45 hvalid hfast

theorem sr8p46:∀ i ∈ List.range 1,StrictCheckAt 8 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 46) 8 46:=by decide +kernel
  have hfast:StrictAtFast (row 8 46) 8 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 46) 8 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 46) 8 46 hvalid hfast

theorem sr8p47:∀ i ∈ List.range 1,StrictCheckAt 8 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 47) 8 47:=by decide +kernel
  have hfast:StrictAtFast (row 8 47) 8 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 47) 8 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 47) 8 47 hvalid hfast

theorem sr8p48:∀ i ∈ List.range 1,StrictCheckAt 8 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 48) 8 48:=by decide +kernel
  have hfast:StrictAtFast (row 8 48) 8 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 48) 8 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 48) 8 48 hvalid hfast

theorem sr8p49:∀ i ∈ List.range 1,StrictCheckAt 8 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 49) 8 49:=by decide +kernel
  have hfast:StrictAtFast (row 8 49) 8 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 49) 8 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 49) 8 49 hvalid hfast

theorem sr8p50:∀ i ∈ List.range 1,StrictCheckAt 8 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 50) 8 50:=by decide +kernel
  have hfast:StrictAtFast (row 8 50) 8 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 50) 8 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 50) 8 50 hvalid hfast

theorem sr8p51:∀ i ∈ List.range 1,StrictCheckAt 8 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 51) 8 51:=by decide +kernel
  have hfast:StrictAtFast (row 8 51) 8 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 51) 8 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 51) 8 51 hvalid hfast

theorem sr8p52:∀ i ∈ List.range 1,StrictCheckAt 8 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 52) 8 52:=by decide +kernel
  have hfast:StrictAtFast (row 8 52) 8 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 52) 8 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 52) 8 52 hvalid hfast

theorem sr8p53:∀ i ∈ List.range 1,StrictCheckAt 8 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 53) 8 53:=by decide +kernel
  have hfast:StrictAtFast (row 8 53) 8 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 53) 8 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 53) 8 53 hvalid hfast

theorem sr8p54:∀ i ∈ List.range 1,StrictCheckAt 8 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 54) 8 54:=by decide +kernel
  have hfast:StrictAtFast (row 8 54) 8 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 54) 8 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 54) 8 54 hvalid hfast

theorem sr8p55:∀ i ∈ List.range 1,StrictCheckAt 8 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 55) 8 55:=by decide +kernel
  have hfast:StrictAtFast (row 8 55) 8 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 55) 8 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 55) 8 55 hvalid hfast

theorem sr8p56:∀ i ∈ List.range 1,StrictCheckAt 8 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 56) 8 56:=by decide +kernel
  have hfast:StrictAtFast (row 8 56) 8 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 56) 8 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 56) 8 56 hvalid hfast

theorem sr8p57:∀ i ∈ List.range 1,StrictCheckAt 8 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 57) 8 57:=by decide +kernel
  have hfast:StrictAtFast (row 8 57) 8 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 57) 8 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 57) 8 57 hvalid hfast

theorem sr8p58:∀ i ∈ List.range 1,StrictCheckAt 8 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 58) 8 58:=by decide +kernel
  have hfast:StrictAtFast (row 8 58) 8 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 58) 8 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 58) 8 58 hvalid hfast

theorem sr8p59:∀ i ∈ List.range 1,StrictCheckAt 8 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 59) 8 59:=by decide +kernel
  have hfast:StrictAtFast (row 8 59) 8 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 59) 8 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 59) 8 59 hvalid hfast

theorem sr8p60:∀ i ∈ List.range 1,StrictCheckAt 8 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 60) 8 60:=by decide +kernel
  have hfast:StrictAtFast (row 8 60) 8 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 60) 8 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 60) 8 60 hvalid hfast

theorem sr8p61:∀ i ∈ List.range 1,StrictCheckAt 8 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 61) 8 61:=by decide +kernel
  have hfast:StrictAtFast (row 8 61) 8 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 61) 8 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 61) 8 61 hvalid hfast

theorem sr8p62:∀ i ∈ List.range 1,StrictCheckAt 8 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 62) 8 62:=by decide +kernel
  have hfast:StrictAtFast (row 8 62) 8 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 62) 8 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 62) 8 62 hvalid hfast

theorem sr8p63:∀ i ∈ List.range 1,StrictCheckAt 8 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 63) 8 63:=by decide +kernel
  have hfast:StrictAtFast (row 8 63) 8 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 63) 8 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 63) 8 63 hvalid hfast

theorem sr8p64:∀ i ∈ List.range 1,StrictCheckAt 8 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 64) 8 64:=by decide +kernel
  have hfast:StrictAtFast (row 8 64) 8 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 64) 8 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 64) 8 64 hvalid hfast

theorem sr8p65:∀ i ∈ List.range 1,StrictCheckAt 8 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 65) 8 65:=by decide +kernel
  have hfast:StrictAtFast (row 8 65) 8 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 65) 8 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 65) 8 65 hvalid hfast

theorem sr8p66:∀ i ∈ List.range 1,StrictCheckAt 8 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 66) 8 66:=by decide +kernel
  have hfast:StrictAtFast (row 8 66) 8 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 66) 8 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 66) 8 66 hvalid hfast

theorem sr8p67:∀ i ∈ List.range 1,StrictCheckAt 8 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 67) 8 67:=by decide +kernel
  have hfast:StrictAtFast (row 8 67) 8 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 67) 8 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 67) 8 67 hvalid hfast

theorem sr8p68:∀ i ∈ List.range 1,StrictCheckAt 8 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 68) 8 68:=by decide +kernel
  have hfast:StrictAtFast (row 8 68) 8 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 68) 8 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 68) 8 68 hvalid hfast

theorem sr8p69:∀ i ∈ List.range 1,StrictCheckAt 8 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 69) 8 69:=by decide +kernel
  have hfast:StrictAtFast (row 8 69) 8 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 69) 8 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 69) 8 69 hvalid hfast

theorem sr8p70:∀ i ∈ List.range 1,StrictCheckAt 8 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 70) 8 70:=by decide +kernel
  have hfast:StrictAtFast (row 8 70) 8 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 70) 8 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 70) 8 70 hvalid hfast

theorem sr8p71:∀ i ∈ List.range 1,StrictCheckAt 8 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 71) 8 71:=by decide +kernel
  have hfast:StrictAtFast (row 8 71) 8 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 71) 8 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 71) 8 71 hvalid hfast

theorem sr8p72:∀ i ∈ List.range 1,StrictCheckAt 8 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 72) 8 72:=by decide +kernel
  have hfast:StrictAtFast (row 8 72) 8 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 72) 8 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 72) 8 72 hvalid hfast

theorem sr8p73:∀ i ∈ List.range 1,StrictCheckAt 8 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 73) 8 73:=by decide +kernel
  have hfast:StrictAtFast (row 8 73) 8 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 73) 8 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 73) 8 73 hvalid hfast

theorem sr8p74:∀ i ∈ List.range 1,StrictCheckAt 8 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 74) 8 74:=by decide +kernel
  have hfast:StrictAtFast (row 8 74) 8 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 74) 8 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 74) 8 74 hvalid hfast

theorem sr8p75:∀ i ∈ List.range 1,StrictCheckAt 8 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 75) 8 75:=by decide +kernel
  have hfast:StrictAtFast (row 8 75) 8 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 75) 8 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 75) 8 75 hvalid hfast

theorem sr8p76:∀ i ∈ List.range 1,StrictCheckAt 8 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 76) 8 76:=by decide +kernel
  have hfast:StrictAtFast (row 8 76) 8 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 76) 8 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 76) 8 76 hvalid hfast

theorem sr8p77:∀ i ∈ List.range 1,StrictCheckAt 8 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 77) 8 77:=by decide +kernel
  have hfast:StrictAtFast (row 8 77) 8 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 77) 8 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 77) 8 77 hvalid hfast

theorem sr8p78:∀ i ∈ List.range 1,StrictCheckAt 8 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 78) 8 78:=by decide +kernel
  have hfast:StrictAtFast (row 8 78) 8 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 78) 8 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 78) 8 78 hvalid hfast

theorem sr8p79:∀ i ∈ List.range 1,StrictCheckAt 8 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 79) 8 79:=by decide +kernel
  have hfast:StrictAtFast (row 8 79) 8 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 79) 8 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 79) 8 79 hvalid hfast

theorem sr8p80:∀ i ∈ List.range 1,StrictCheckAt 8 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 80) 8 80:=by decide +kernel
  have hfast:StrictAtFast (row 8 80) 8 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 80) 8 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 80) 8 80 hvalid hfast

theorem sr8p81:∀ i ∈ List.range 1,StrictCheckAt 8 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 81) 8 81:=by decide +kernel
  have hfast:StrictAtFast (row 8 81) 8 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 81) 8 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 81) 8 81 hvalid hfast

theorem sr8p82:∀ i ∈ List.range 1,StrictCheckAt 8 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 82) 8 82:=by decide +kernel
  have hfast:StrictAtFast (row 8 82) 8 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 82) 8 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 82) 8 82 hvalid hfast

theorem sr8p83:∀ i ∈ List.range 1,StrictCheckAt 8 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 83) 8 83:=by decide +kernel
  have hfast:StrictAtFast (row 8 83) 8 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 83) 8 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 83) 8 83 hvalid hfast

theorem sr8p84:∀ i ∈ List.range 1,StrictCheckAt 8 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 84) 8 84:=by decide +kernel
  have hfast:StrictAtFast (row 8 84) 8 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 84) 8 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 84) 8 84 hvalid hfast

theorem sr8p85:∀ i ∈ List.range 1,StrictCheckAt 8 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 85) 8 85:=by decide +kernel
  have hfast:StrictAtFast (row 8 85) 8 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 85) 8 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 85) 8 85 hvalid hfast

theorem sr8p86:∀ i ∈ List.range 1,StrictCheckAt 8 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 86) 8 86:=by decide +kernel
  have hfast:StrictAtFast (row 8 86) 8 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 86) 8 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 86) 8 86 hvalid hfast

theorem sr8p87:∀ i ∈ List.range 1,StrictCheckAt 8 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 87) 8 87:=by decide +kernel
  have hfast:StrictAtFast (row 8 87) 8 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 87) 8 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 87) 8 87 hvalid hfast

theorem sr8p88:∀ i ∈ List.range 1,StrictCheckAt 8 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 88) 8 88:=by decide +kernel
  have hfast:StrictAtFast (row 8 88) 8 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 88) 8 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 88) 8 88 hvalid hfast

theorem sr8p89:∀ i ∈ List.range 1,StrictCheckAt 8 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 89) 8 89:=by decide +kernel
  have hfast:StrictAtFast (row 8 89) 8 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 89) 8 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 89) 8 89 hvalid hfast

theorem sr8p90:∀ i ∈ List.range 1,StrictCheckAt 8 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 90) 8 90:=by decide +kernel
  have hfast:StrictAtFast (row 8 90) 8 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 90) 8 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 90) 8 90 hvalid hfast

theorem sr8p91:∀ i ∈ List.range 1,StrictCheckAt 8 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 91) 8 91:=by decide +kernel
  have hfast:StrictAtFast (row 8 91) 8 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 91) 8 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 91) 8 91 hvalid hfast

theorem sr8p92:∀ i ∈ List.range 1,StrictCheckAt 8 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 92) 8 92:=by decide +kernel
  have hfast:StrictAtFast (row 8 92) 8 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 92) 8 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 92) 8 92 hvalid hfast

theorem sr8p93:∀ i ∈ List.range 1,StrictCheckAt 8 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 93) 8 93:=by decide +kernel
  have hfast:StrictAtFast (row 8 93) 8 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 93) 8 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 93) 8 93 hvalid hfast

theorem sr8p94:∀ i ∈ List.range 1,StrictCheckAt 8 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 94) 8 94:=by decide +kernel
  have hfast:StrictAtFast (row 8 94) 8 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 94) 8 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 94) 8 94 hvalid hfast

theorem sr8p95:∀ i ∈ List.range 1,StrictCheckAt 8 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 95) 8 95:=by decide +kernel
  have hfast:StrictAtFast (row 8 95) 8 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 95) 8 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 95) 8 95 hvalid hfast

theorem sr8p96:∀ i ∈ List.range 1,StrictCheckAt 8 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 96) 8 96:=by decide +kernel
  have hfast:StrictAtFast (row 8 96) 8 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 96) 8 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 96) 8 96 hvalid hfast

theorem sr8p97:∀ i ∈ List.range 1,StrictCheckAt 8 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 97) 8 97:=by decide +kernel
  have hfast:StrictAtFast (row 8 97) 8 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 97) 8 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 97) 8 97 hvalid hfast

theorem sr8p98:∀ i ∈ List.range 1,StrictCheckAt 8 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 98) 8 98:=by decide +kernel
  have hfast:StrictAtFast (row 8 98) 8 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 98) 8 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 98) 8 98 hvalid hfast

theorem sr8p99:∀ i ∈ List.range 1,StrictCheckAt 8 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 99) 8 99:=by decide +kernel
  have hfast:StrictAtFast (row 8 99) 8 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 99) 8 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 99) 8 99 hvalid hfast

theorem sr8p100:∀ i ∈ List.range 1,StrictCheckAt 8 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 100) 8 100:=by decide +kernel
  have hfast:StrictAtFast (row 8 100) 8 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 100) 8 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 100) 8 100 hvalid hfast

theorem sr8p101:∀ i ∈ List.range 1,StrictCheckAt 8 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 101) 8 101:=by decide +kernel
  have hfast:StrictAtFast (row 8 101) 8 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 101) 8 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 101) 8 101 hvalid hfast

theorem sr8p102:∀ i ∈ List.range 1,StrictCheckAt 8 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 102) 8 102:=by decide +kernel
  have hfast:StrictAtFast (row 8 102) 8 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 102) 8 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 102) 8 102 hvalid hfast

theorem sr8p103:∀ i ∈ List.range 1,StrictCheckAt 8 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 103) 8 103:=by decide +kernel
  have hfast:StrictAtFast (row 8 103) 8 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 103) 8 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 103) 8 103 hvalid hfast

theorem sr8p104:∀ i ∈ List.range 1,StrictCheckAt 8 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 104) 8 104:=by decide +kernel
  have hfast:StrictAtFast (row 8 104) 8 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 104) 8 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 104) 8 104 hvalid hfast

theorem sr8p105:∀ i ∈ List.range 1,StrictCheckAt 8 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 105) 8 105:=by decide +kernel
  have hfast:StrictAtFast (row 8 105) 8 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 105) 8 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 105) 8 105 hvalid hfast

theorem sr8p106:∀ i ∈ List.range 1,StrictCheckAt 8 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 106) 8 106:=by decide +kernel
  have hfast:StrictAtFast (row 8 106) 8 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 106) 8 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 106) 8 106 hvalid hfast

theorem sr8p107:∀ i ∈ List.range 1,StrictCheckAt 8 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 107) 8 107:=by decide +kernel
  have hfast:StrictAtFast (row 8 107) 8 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 107) 8 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 107) 8 107 hvalid hfast

theorem sr8p108:∀ i ∈ List.range 1,StrictCheckAt 8 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 108) 8 108:=by decide +kernel
  have hfast:StrictAtFast (row 8 108) 8 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 108) 8 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 108) 8 108 hvalid hfast

theorem sr8p109:∀ i ∈ List.range 1,StrictCheckAt 8 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 109) 8 109:=by decide +kernel
  have hfast:StrictAtFast (row 8 109) 8 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 109) 8 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 109) 8 109 hvalid hfast

theorem sr8p110:∀ i ∈ List.range 1,StrictCheckAt 8 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 110) 8 110:=by decide +kernel
  have hfast:StrictAtFast (row 8 110) 8 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 110) 8 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 110) 8 110 hvalid hfast

theorem sr8p111:∀ i ∈ List.range 1,StrictCheckAt 8 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 111) 8 111:=by decide +kernel
  have hfast:StrictAtFast (row 8 111) 8 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 111) 8 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 111) 8 111 hvalid hfast

theorem sr8p112:∀ i ∈ List.range 1,StrictCheckAt 8 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 112) 8 112:=by decide +kernel
  have hfast:StrictAtFast (row 8 112) 8 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 112) 8 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 112) 8 112 hvalid hfast

theorem sr8p113:∀ i ∈ List.range 1,StrictCheckAt 8 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 113) 8 113:=by decide +kernel
  have hfast:StrictAtFast (row 8 113) 8 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 113) 8 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 113) 8 113 hvalid hfast

theorem sr8p114:∀ i ∈ List.range 1,StrictCheckAt 8 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 114) 8 114:=by decide +kernel
  have hfast:StrictAtFast (row 8 114) 8 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 114) 8 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 114) 8 114 hvalid hfast

theorem sr8p115:∀ i ∈ List.range 1,StrictCheckAt 8 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 115) 8 115:=by decide +kernel
  have hfast:StrictAtFast (row 8 115) 8 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 115) 8 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 115) 8 115 hvalid hfast

theorem sr8p116:∀ i ∈ List.range 1,StrictCheckAt 8 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 116) 8 116:=by decide +kernel
  have hfast:StrictAtFast (row 8 116) 8 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 116) 8 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 116) 8 116 hvalid hfast

theorem sr8p117:∀ i ∈ List.range 1,StrictCheckAt 8 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 117) 8 117:=by decide +kernel
  have hfast:StrictAtFast (row 8 117) 8 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 117) 8 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 117) 8 117 hvalid hfast

theorem sr8p118:∀ i ∈ List.range 1,StrictCheckAt 8 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 118) 8 118:=by decide +kernel
  have hfast:StrictAtFast (row 8 118) 8 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 118) 8 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 118) 8 118 hvalid hfast

theorem sr8p119:∀ i ∈ List.range 1,StrictCheckAt 8 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 119) 8 119:=by decide +kernel
  have hfast:StrictAtFast (row 8 119) 8 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 119) 8 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 119) 8 119 hvalid hfast

theorem sr8p120:∀ i ∈ List.range 1,StrictCheckAt 8 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 120) 8 120:=by decide +kernel
  have hfast:StrictAtFast (row 8 120) 8 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 120) 8 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 120) 8 120 hvalid hfast

theorem sr8p121:∀ i ∈ List.range 1,StrictCheckAt 8 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 121) 8 121:=by decide +kernel
  have hfast:StrictAtFast (row 8 121) 8 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 121) 8 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 121) 8 121 hvalid hfast

theorem sr8p122:∀ i ∈ List.range 1,StrictCheckAt 8 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 122) 8 122:=by decide +kernel
  have hfast:StrictAtFast (row 8 122) 8 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 122) 8 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 122) 8 122 hvalid hfast

theorem sr8p123:∀ i ∈ List.range 1,StrictCheckAt 8 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 123) 8 123:=by decide +kernel
  have hfast:StrictAtFast (row 8 123) 8 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 123) 8 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 123) 8 123 hvalid hfast

theorem sr8p124:∀ i ∈ List.range 1,StrictCheckAt 8 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 124) 8 124:=by decide +kernel
  have hfast:StrictAtFast (row 8 124) 8 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 124) 8 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 124) 8 124 hvalid hfast

theorem sr8p125:∀ i ∈ List.range 1,StrictCheckAt 8 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 125) 8 125:=by decide +kernel
  have hfast:StrictAtFast (row 8 125) 8 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 125) 8 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 125) 8 125 hvalid hfast

theorem sr8p126:∀ i ∈ List.range 1,StrictCheckAt 8 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 126) 8 126:=by decide +kernel
  have hfast:StrictAtFast (row 8 126) 8 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 126) 8 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 126) 8 126 hvalid hfast

theorem sr8p127:∀ i ∈ List.range 1,StrictCheckAt 8 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 127) 8 127:=by decide +kernel
  have hfast:StrictAtFast (row 8 127) 8 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 127) 8 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 127) 8 127 hvalid hfast

theorem sr8p128:∀ i ∈ List.range 1,StrictCheckAt 8 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 128) 8 128:=by decide +kernel
  have hfast:StrictAtFast (row 8 128) 8 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 128) 8 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 128) 8 128 hvalid hfast

theorem sr8p129:∀ i ∈ List.range 1,StrictCheckAt 8 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 129) 8 129:=by decide +kernel
  have hfast:StrictAtFast (row 8 129) 8 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 129) 8 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 129) 8 129 hvalid hfast

theorem sr8p130:∀ i ∈ List.range 1,StrictCheckAt 8 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 130) 8 130:=by decide +kernel
  have hfast:StrictAtFast (row 8 130) 8 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 130) 8 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 130) 8 130 hvalid hfast

theorem sr8p131:∀ i ∈ List.range 1,StrictCheckAt 8 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 131 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 131) 8 131:=by decide +kernel
  have hfast:StrictAtFast (row 8 131) 8 131:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 131) 8 131 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 131) 8 131 hvalid hfast

theorem sr8p132:∀ i ∈ List.range 1,StrictCheckAt 8 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 132 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 132) 8 132:=by decide +kernel
  have hfast:StrictAtFast (row 8 132) 8 132:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 132) 8 132 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 132) 8 132 hvalid hfast

theorem sr8p133:∀ i ∈ List.range 1,StrictCheckAt 8 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 133 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 133) 8 133:=by decide +kernel
  have hfast:StrictAtFast (row 8 133) 8 133:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 133) 8 133 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 133) 8 133 hvalid hfast

theorem sr8p134:∀ i ∈ List.range 1,StrictCheckAt 8 (134+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 134 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 134) 8 134:=by decide +kernel
  have hfast:StrictAtFast (row 8 134) 8 134:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 134) 8 134 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 134) 8 134 hvalid hfast

theorem br8p0:∀ i ∈ List.range 4,BaseCheckAt 8 (0+i):=by decide +kernel

theorem br8p1:∀ i ∈ List.range 4,BaseCheckAt 8 (4+i):=by decide +kernel

theorem br8p2:∀ i ∈ List.range 4,BaseCheckAt 8 (8+i):=by decide +kernel

theorem br8p3:∀ i ∈ List.range 4,BaseCheckAt 8 (12+i):=by decide +kernel

theorem br8p4:∀ i ∈ List.range 4,BaseCheckAt 8 (16+i):=by decide +kernel

theorem br8p5:∀ i ∈ List.range 4,BaseCheckAt 8 (20+i):=by decide +kernel

theorem br8p6:∀ i ∈ List.range 4,BaseCheckAt 8 (24+i):=by decide +kernel

theorem br8p7:∀ i ∈ List.range 4,BaseCheckAt 8 (28+i):=by decide +kernel

theorem br8p8:∀ i ∈ List.range 4,BaseCheckAt 8 (32+i):=by decide +kernel

theorem br8p9:∀ i ∈ List.range 4,BaseCheckAt 8 (36+i):=by decide +kernel

theorem br8p10:∀ i ∈ List.range 4,BaseCheckAt 8 (40+i):=by decide +kernel

theorem br8p11:∀ i ∈ List.range 4,BaseCheckAt 8 (44+i):=by decide +kernel

theorem br8p12:∀ i ∈ List.range 4,BaseCheckAt 8 (48+i):=by decide +kernel

theorem br8p13:∀ i ∈ List.range 4,BaseCheckAt 8 (52+i):=by decide +kernel

theorem br8p14:∀ i ∈ List.range 4,BaseCheckAt 8 (56+i):=by decide +kernel

theorem br8p15:∀ i ∈ List.range 4,BaseCheckAt 8 (60+i):=by decide +kernel



theorem br8p16:∀ i ∈ List.range 4,BaseCheckAt 8 (64+i):=by decide +kernel

theorem br8p17:∀ i ∈ List.range 4,BaseCheckAt 8 (68+i):=by decide +kernel

theorem br8p18:∀ i ∈ List.range 4,BaseCheckAt 8 (72+i):=by decide +kernel

theorem br8p19:∀ i ∈ List.range 4,BaseCheckAt 8 (76+i):=by decide +kernel

theorem br8p20:∀ i ∈ List.range 4,BaseCheckAt 8 (80+i):=by decide +kernel

theorem br8p21:∀ i ∈ List.range 4,BaseCheckAt 8 (84+i):=by decide +kernel

theorem br8p22:∀ i ∈ List.range 4,BaseCheckAt 8 (88+i):=by decide +kernel

theorem br8p23:∀ i ∈ List.range 4,BaseCheckAt 8 (92+i):=by decide +kernel

theorem br8p24:∀ i ∈ List.range 4,BaseCheckAt 8 (96+i):=by decide +kernel

theorem br8p25:∀ i ∈ List.range 4,BaseCheckAt 8 (100+i):=by decide +kernel

theorem br8p26:∀ i ∈ List.range 4,BaseCheckAt 8 (104+i):=by decide +kernel

theorem br8p27:∀ i ∈ List.range 4,BaseCheckAt 8 (108+i):=by decide +kernel

theorem br8p28:∀ i ∈ List.range 4,BaseCheckAt 8 (112+i):=by decide +kernel

theorem br8p29:∀ i ∈ List.range 4,BaseCheckAt 8 (116+i):=by decide +kernel

theorem br8p30:∀ i ∈ List.range 4,BaseCheckAt 8 (120+i):=by decide +kernel

theorem br8p31:∀ i ∈ List.range 4,BaseCheckAt 8 (124+i):=by decide +kernel



theorem br8p32:∀ i ∈ List.range 4,BaseCheckAt 8 (128+i):=by decide +kernel

theorem br8p33:∀ i ∈ List.range 3,BaseCheckAt 8 (132+i):=by decide +kernel



theorem cr8:∀ V ∈ List.range 135,CorrectAt 8 V:=by
  intro V hV
  have hv:V < 135:=List.mem_range.mp hV
  by_cases h0_17:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr8p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr8p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr8p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr8p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr8p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr8p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr8p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr8p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_17:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr8p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr8p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr8p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr8p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_17:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr8p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr8p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_17:V < 120
        · have h:=cr8p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h15_17:V < 128
          · have h:=cr8p15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=cr8p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem zr8:∀ V ∈ List.range 135,ZeroCheckAt 8 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 8 V (by omega) (by omega) (by omega)
theorem sr8:∀ V ∈ List.range 135,StrictCheckAt 8 V:=by
  intro V hV
  have hv:V < 135:=List.mem_range.mp hV
  by_cases h0_135:V < 67
  · by_cases h0_67:V < 33
    · by_cases h0_33:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have h:=sr8p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
              · have h:=sr8p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
            · by_cases h2_4:V < 3
              · have h:=sr8p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
              · have h:=sr8p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have h:=sr8p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
              · have h:=sr8p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
            · by_cases h6_8:V < 7
              · have h:=sr8p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
              · have h:=sr8p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have h:=sr8p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr8p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
            · by_cases h10_12:V < 11
              · have h:=sr8p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr8p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have h:=sr8p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr8p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
            · by_cases h14_16:V < 15
              · have h:=sr8p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
              · have h:=sr8p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
      · by_cases h16_33:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have h:=sr8p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr8p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
            · by_cases h18_20:V < 19
              · have h:=sr8p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr8p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have h:=sr8p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr8p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr8p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr8p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
        · by_cases h24_33:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr8p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr8p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr8p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr8p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
          · by_cases h28_33:V < 30
            · by_cases h28_30:V < 29
              · have h:=sr8p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr8p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_33:V < 31
              · have h:=sr8p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · by_cases h31_33:V < 32
                · have h:=sr8p31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
                · have h:=sr8p32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
    · by_cases h33_67:V < 50
      · by_cases h33_50:V < 41
        · by_cases h33_41:V < 37
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have h:=sr8p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr8p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
            · by_cases h35_37:V < 36
              · have h:=sr8p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr8p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have h:=sr8p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr8p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
            · by_cases h39_41:V < 40
              · have h:=sr8p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr8p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · by_cases h41_50:V < 45
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have h:=sr8p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr8p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr8p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr8p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · by_cases h45_50:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr8p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr8p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_50:V < 48
              · have h:=sr8p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · by_cases h48_50:V < 49
                · have h:=sr8p48 (V-48) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
                · have h:=sr8p49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
      · by_cases h50_67:V < 58
        · by_cases h50_58:V < 54
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have h:=sr8p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr8p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
            · by_cases h52_54:V < 53
              · have h:=sr8p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr8p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have h:=sr8p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr8p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
            · by_cases h56_58:V < 57
              · have h:=sr8p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr8p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
        · by_cases h58_67:V < 62
          · by_cases h58_62:V < 60
            · by_cases h58_60:V < 59
              · have h:=sr8p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr8p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
            · by_cases h60_62:V < 61
              · have h:=sr8p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr8p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
          · by_cases h62_67:V < 64
            · by_cases h62_64:V < 63
              · have h:=sr8p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr8p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
            · by_cases h64_67:V < 65
              · have h:=sr8p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · by_cases h65_67:V < 66
                · have h:=sr8p65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
                · have h:=sr8p66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
  · by_cases h67_135:V < 101
    · by_cases h67_101:V < 84
      · by_cases h67_84:V < 75
        · by_cases h67_75:V < 71
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have h:=sr8p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr8p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
            · by_cases h69_71:V < 70
              · have h:=sr8p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr8p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have h:=sr8p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr8p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
            · by_cases h73_75:V < 74
              · have h:=sr8p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr8p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
        · by_cases h75_84:V < 79
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have h:=sr8p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr8p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
            · by_cases h77_79:V < 78
              · have h:=sr8p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr8p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
          · by_cases h79_84:V < 81
            · by_cases h79_81:V < 80
              · have h:=sr8p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr8p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
            · by_cases h81_84:V < 82
              · have h:=sr8p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · by_cases h82_84:V < 83
                · have h:=sr8p82 (V-82) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
                · have h:=sr8p83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
      · by_cases h84_101:V < 92
        · by_cases h84_92:V < 88
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have h:=sr8p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr8p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
            · by_cases h86_88:V < 87
              · have h:=sr8p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr8p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have h:=sr8p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr8p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
            · by_cases h90_92:V < 91
              · have h:=sr8p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr8p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
        · by_cases h92_101:V < 96
          · by_cases h92_96:V < 94
            · by_cases h92_94:V < 93
              · have h:=sr8p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr8p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
            · by_cases h94_96:V < 95
              · have h:=sr8p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr8p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
          · by_cases h96_101:V < 98
            · by_cases h96_98:V < 97
              · have h:=sr8p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr8p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
            · by_cases h98_101:V < 99
              · have h:=sr8p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · by_cases h99_101:V < 100
                · have h:=sr8p99 (V-99) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
                · have h:=sr8p100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
    · by_cases h101_135:V < 118
      · by_cases h101_118:V < 109
        · by_cases h101_109:V < 105
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have h:=sr8p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr8p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr8p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr8p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have h:=sr8p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr8p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
            · by_cases h107_109:V < 108
              · have h:=sr8p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr8p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
        · by_cases h109_118:V < 113
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have h:=sr8p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr8p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
            · by_cases h111_113:V < 112
              · have h:=sr8p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr8p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · by_cases h113_118:V < 115
            · by_cases h113_115:V < 114
              · have h:=sr8p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr8p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
            · by_cases h115_118:V < 116
              · have h:=sr8p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · by_cases h116_118:V < 117
                · have h:=sr8p116 (V-116) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
                · have h:=sr8p117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
      · by_cases h118_135:V < 126
        · by_cases h118_126:V < 122
          · by_cases h118_122:V < 120
            · by_cases h118_120:V < 119
              · have h:=sr8p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr8p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
            · by_cases h120_122:V < 121
              · have h:=sr8p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
              · have h:=sr8p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
          · by_cases h122_126:V < 124
            · by_cases h122_124:V < 123
              · have h:=sr8p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
              · have h:=sr8p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
            · by_cases h124_126:V < 125
              · have h:=sr8p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
              · have h:=sr8p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
        · by_cases h126_135:V < 130
          · by_cases h126_130:V < 128
            · by_cases h126_128:V < 127
              · have h:=sr8p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h
              · have h:=sr8p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using h
            · by_cases h128_130:V < 129
              · have h:=sr8p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
              · have h:=sr8p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using h
          · by_cases h130_135:V < 132
            · by_cases h130_132:V < 131
              · have h:=sr8p130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using h
              · have h:=sr8p131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using h
            · by_cases h132_135:V < 133
              · have h:=sr8p132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using h
              · by_cases h133_135:V < 134
                · have h:=sr8p133 (V-133) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using h
                · have h:=sr8p134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using h

theorem br8:∀ V ∈ List.range 135,BaseCheckAt 8 V:=by
  intro V hV
  have hv:V < 135:=List.mem_range.mp hV
  by_cases h0_34:V < 68
  · by_cases h0_17:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br8p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br8p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br8p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br8p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br8p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br8p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br8p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br8p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_17:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br8p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br8p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br8p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br8p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_17:V < 56
        · by_cases h12_14:V < 52
          · have h:=br8p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br8p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_17:V < 60
          · have h:=br8p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · by_cases h15_17:V < 64
            · have h:=br8p15 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · have h:=br8p16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
  · by_cases h17_34:V < 100
    · by_cases h17_25:V < 84
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br8p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br8p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br8p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br8p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
      · by_cases h21_25:V < 92
        · by_cases h21_23:V < 88
          · have h:=br8p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br8p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h23_25:V < 96
          · have h:=br8p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br8p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
    · by_cases h25_34:V < 116
      · by_cases h25_29:V < 108
        · by_cases h25_27:V < 104
          · have h:=br8p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br8p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h27_29:V < 112
          · have h:=br8p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br8p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
      · by_cases h29_34:V < 124
        · by_cases h29_31:V < 120
          · have h:=br8p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · have h:=br8p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
        · by_cases h31_34:V < 128
          · have h:=br8p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
          · by_cases h32_34:V < 132
            · have h:=br8p32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
            · have h:=br8p33 (V-132) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
