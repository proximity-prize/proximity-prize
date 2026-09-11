import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
