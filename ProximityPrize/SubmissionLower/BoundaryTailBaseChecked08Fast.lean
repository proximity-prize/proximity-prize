import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
