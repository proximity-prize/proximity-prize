import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr9p0:∀ i ∈ List.range 8,CorrectAt 9 (0+i):=by decide +kernel

theorem cr9p1:∀ i ∈ List.range 8,CorrectAt 9 (8+i):=by decide +kernel

theorem cr9p2:∀ i ∈ List.range 8,CorrectAt 9 (16+i):=by decide +kernel

theorem cr9p3:∀ i ∈ List.range 8,CorrectAt 9 (24+i):=by decide +kernel

theorem cr9p4:∀ i ∈ List.range 8,CorrectAt 9 (32+i):=by decide +kernel

theorem cr9p5:∀ i ∈ List.range 8,CorrectAt 9 (40+i):=by decide +kernel

theorem cr9p6:∀ i ∈ List.range 8,CorrectAt 9 (48+i):=by decide +kernel

theorem cr9p7:∀ i ∈ List.range 8,CorrectAt 9 (56+i):=by decide +kernel

theorem cr9p8:∀ i ∈ List.range 8,CorrectAt 9 (64+i):=by decide +kernel

theorem cr9p9:∀ i ∈ List.range 8,CorrectAt 9 (72+i):=by decide +kernel

theorem cr9p10:∀ i ∈ List.range 8,CorrectAt 9 (80+i):=by decide +kernel

theorem cr9p11:∀ i ∈ List.range 8,CorrectAt 9 (88+i):=by decide +kernel

theorem cr9p12:∀ i ∈ List.range 8,CorrectAt 9 (96+i):=by decide +kernel

theorem cr9p13:∀ i ∈ List.range 8,CorrectAt 9 (104+i):=by decide +kernel

theorem cr9p14:∀ i ∈ List.range 8,CorrectAt 9 (112+i):=by decide +kernel

theorem cr9p15:∀ i ∈ List.range 8,CorrectAt 9 (120+i):=by decide +kernel

theorem cr9p16:∀ i ∈ List.range 6,CorrectAt 9 (128+i):=by decide +kernel

theorem sr9p0:∀ i ∈ List.range 1,StrictCheckAt 9 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 0) 9 0:=by decide +kernel
  have hfast:StrictAtFast (row 9 0) 9 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 0) 9 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 0) 9 0 hvalid hfast

theorem sr9p1:∀ i ∈ List.range 1,StrictCheckAt 9 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 1) 9 1:=by decide +kernel
  have hfast:StrictAtFast (row 9 1) 9 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 1) 9 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 1) 9 1 hvalid hfast

theorem sr9p2:∀ i ∈ List.range 1,StrictCheckAt 9 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 2) 9 2:=by decide +kernel
  have hfast:StrictAtFast (row 9 2) 9 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 2) 9 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 2) 9 2 hvalid hfast

theorem sr9p3:∀ i ∈ List.range 1,StrictCheckAt 9 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 3) 9 3:=by decide +kernel
  have hfast:StrictAtFast (row 9 3) 9 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 3) 9 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 3) 9 3 hvalid hfast

theorem sr9p4:∀ i ∈ List.range 1,StrictCheckAt 9 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 4) 9 4:=by decide +kernel
  have hfast:StrictAtFast (row 9 4) 9 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 4) 9 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 4) 9 4 hvalid hfast

theorem sr9p5:∀ i ∈ List.range 1,StrictCheckAt 9 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 5) 9 5:=by decide +kernel
  have hfast:StrictAtFast (row 9 5) 9 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 5) 9 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 5) 9 5 hvalid hfast

theorem sr9p6:∀ i ∈ List.range 1,StrictCheckAt 9 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 6) 9 6:=by decide +kernel
  have hfast:StrictAtFast (row 9 6) 9 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 6) 9 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 6) 9 6 hvalid hfast

theorem sr9p7:∀ i ∈ List.range 1,StrictCheckAt 9 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 7) 9 7:=by decide +kernel
  have hfast:StrictAtFast (row 9 7) 9 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 7) 9 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 7) 9 7 hvalid hfast

theorem sr9p8:∀ i ∈ List.range 1,StrictCheckAt 9 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 8) 9 8:=by decide +kernel
  have hfast:StrictAtFast (row 9 8) 9 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 8) 9 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 8) 9 8 hvalid hfast

theorem sr9p9:∀ i ∈ List.range 1,StrictCheckAt 9 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 9) 9 9:=by decide +kernel
  have hfast:StrictAtFast (row 9 9) 9 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 9) 9 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 9) 9 9 hvalid hfast

theorem sr9p10:∀ i ∈ List.range 1,StrictCheckAt 9 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 10) 9 10:=by decide +kernel
  have hfast:StrictAtFast (row 9 10) 9 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 10) 9 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 10) 9 10 hvalid hfast

theorem sr9p11:∀ i ∈ List.range 1,StrictCheckAt 9 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 11) 9 11:=by decide +kernel
  have hfast:StrictAtFast (row 9 11) 9 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 11) 9 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 11) 9 11 hvalid hfast

theorem sr9p12:∀ i ∈ List.range 1,StrictCheckAt 9 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 12) 9 12:=by decide +kernel
  have hfast:StrictAtFast (row 9 12) 9 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 12) 9 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 12) 9 12 hvalid hfast

theorem sr9p13:∀ i ∈ List.range 1,StrictCheckAt 9 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 13) 9 13:=by decide +kernel
  have hfast:StrictAtFast (row 9 13) 9 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 13) 9 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 13) 9 13 hvalid hfast

theorem sr9p14:∀ i ∈ List.range 1,StrictCheckAt 9 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 14) 9 14:=by decide +kernel
  have hfast:StrictAtFast (row 9 14) 9 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 14) 9 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 14) 9 14 hvalid hfast

theorem sr9p15:∀ i ∈ List.range 1,StrictCheckAt 9 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 15) 9 15:=by decide +kernel
  have hfast:StrictAtFast (row 9 15) 9 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 15) 9 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 15) 9 15 hvalid hfast

theorem sr9p16:∀ i ∈ List.range 1,StrictCheckAt 9 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 16) 9 16:=by decide +kernel
  have hfast:StrictAtFast (row 9 16) 9 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 16) 9 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 16) 9 16 hvalid hfast

theorem sr9p17:∀ i ∈ List.range 1,StrictCheckAt 9 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 17) 9 17:=by decide +kernel
  have hfast:StrictAtFast (row 9 17) 9 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 17) 9 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 17) 9 17 hvalid hfast

theorem sr9p18:∀ i ∈ List.range 1,StrictCheckAt 9 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 18) 9 18:=by decide +kernel
  have hfast:StrictAtFast (row 9 18) 9 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 18) 9 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 18) 9 18 hvalid hfast

theorem sr9p19:∀ i ∈ List.range 1,StrictCheckAt 9 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 19) 9 19:=by decide +kernel
  have hfast:StrictAtFast (row 9 19) 9 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 19) 9 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 19) 9 19 hvalid hfast

theorem sr9p20:∀ i ∈ List.range 1,StrictCheckAt 9 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 20) 9 20:=by decide +kernel
  have hfast:StrictAtFast (row 9 20) 9 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 20) 9 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 20) 9 20 hvalid hfast

theorem sr9p21:∀ i ∈ List.range 1,StrictCheckAt 9 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 21) 9 21:=by decide +kernel
  have hfast:StrictAtFast (row 9 21) 9 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 21) 9 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 21) 9 21 hvalid hfast

theorem sr9p22:∀ i ∈ List.range 1,StrictCheckAt 9 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 22) 9 22:=by decide +kernel
  have hfast:StrictAtFast (row 9 22) 9 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 22) 9 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 22) 9 22 hvalid hfast

theorem sr9p23:∀ i ∈ List.range 1,StrictCheckAt 9 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 23) 9 23:=by decide +kernel
  have hfast:StrictAtFast (row 9 23) 9 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 23) 9 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 23) 9 23 hvalid hfast

theorem sr9p24:∀ i ∈ List.range 1,StrictCheckAt 9 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 24) 9 24:=by decide +kernel
  have hfast:StrictAtFast (row 9 24) 9 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 24) 9 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 24) 9 24 hvalid hfast

theorem sr9p25:∀ i ∈ List.range 1,StrictCheckAt 9 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 25) 9 25:=by decide +kernel
  have hfast:StrictAtFast (row 9 25) 9 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 25) 9 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 25) 9 25 hvalid hfast

theorem sr9p26:∀ i ∈ List.range 1,StrictCheckAt 9 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 26) 9 26:=by decide +kernel
  have hfast:StrictAtFast (row 9 26) 9 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 26) 9 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 26) 9 26 hvalid hfast

theorem sr9p27:∀ i ∈ List.range 1,StrictCheckAt 9 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 27) 9 27:=by decide +kernel
  have hfast:StrictAtFast (row 9 27) 9 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 27) 9 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 27) 9 27 hvalid hfast

theorem sr9p28:∀ i ∈ List.range 1,StrictCheckAt 9 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 28) 9 28:=by decide +kernel
  have hfast:StrictAtFast (row 9 28) 9 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 28) 9 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 28) 9 28 hvalid hfast

theorem sr9p29:∀ i ∈ List.range 1,StrictCheckAt 9 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 29) 9 29:=by decide +kernel
  have hfast:StrictAtFast (row 9 29) 9 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 29) 9 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 29) 9 29 hvalid hfast

theorem sr9p30:∀ i ∈ List.range 1,StrictCheckAt 9 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 30) 9 30:=by decide +kernel
  have hfast:StrictAtFast (row 9 30) 9 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 30) 9 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 30) 9 30 hvalid hfast

theorem sr9p31:∀ i ∈ List.range 1,StrictCheckAt 9 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 31) 9 31:=by decide +kernel
  have hfast:StrictAtFast (row 9 31) 9 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 31) 9 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 31) 9 31 hvalid hfast

theorem sr9p32:∀ i ∈ List.range 1,StrictCheckAt 9 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 32) 9 32:=by decide +kernel
  have hfast:StrictAtFast (row 9 32) 9 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 32) 9 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 32) 9 32 hvalid hfast

theorem sr9p33:∀ i ∈ List.range 1,StrictCheckAt 9 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 33) 9 33:=by decide +kernel
  have hfast:StrictAtFast (row 9 33) 9 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 33) 9 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 33) 9 33 hvalid hfast

theorem sr9p34:∀ i ∈ List.range 1,StrictCheckAt 9 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 34) 9 34:=by decide +kernel
  have hfast:StrictAtFast (row 9 34) 9 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 34) 9 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 34) 9 34 hvalid hfast

theorem sr9p35:∀ i ∈ List.range 1,StrictCheckAt 9 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 35) 9 35:=by decide +kernel
  have hfast:StrictAtFast (row 9 35) 9 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 35) 9 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 35) 9 35 hvalid hfast

theorem sr9p36:∀ i ∈ List.range 1,StrictCheckAt 9 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 36) 9 36:=by decide +kernel
  have hfast:StrictAtFast (row 9 36) 9 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 36) 9 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 36) 9 36 hvalid hfast

theorem sr9p37:∀ i ∈ List.range 1,StrictCheckAt 9 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 37) 9 37:=by decide +kernel
  have hfast:StrictAtFast (row 9 37) 9 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 37) 9 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 37) 9 37 hvalid hfast

theorem sr9p38:∀ i ∈ List.range 1,StrictCheckAt 9 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 38) 9 38:=by decide +kernel
  have hfast:StrictAtFast (row 9 38) 9 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 38) 9 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 38) 9 38 hvalid hfast

theorem sr9p39:∀ i ∈ List.range 1,StrictCheckAt 9 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 39) 9 39:=by decide +kernel
  have hfast:StrictAtFast (row 9 39) 9 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 39) 9 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 39) 9 39 hvalid hfast

theorem sr9p40:∀ i ∈ List.range 1,StrictCheckAt 9 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 40) 9 40:=by decide +kernel
  have hfast:StrictAtFast (row 9 40) 9 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 40) 9 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 40) 9 40 hvalid hfast

theorem sr9p41:∀ i ∈ List.range 1,StrictCheckAt 9 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 41) 9 41:=by decide +kernel
  have hfast:StrictAtFast (row 9 41) 9 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 41) 9 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 41) 9 41 hvalid hfast

theorem sr9p42:∀ i ∈ List.range 1,StrictCheckAt 9 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 42) 9 42:=by decide +kernel
  have hfast:StrictAtFast (row 9 42) 9 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 42) 9 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 42) 9 42 hvalid hfast

theorem sr9p43:∀ i ∈ List.range 1,StrictCheckAt 9 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 43) 9 43:=by decide +kernel
  have hfast:StrictAtFast (row 9 43) 9 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 43) 9 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 43) 9 43 hvalid hfast

theorem sr9p44:∀ i ∈ List.range 1,StrictCheckAt 9 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 44) 9 44:=by decide +kernel
  have hfast:StrictAtFast (row 9 44) 9 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 44) 9 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 44) 9 44 hvalid hfast

theorem sr9p45:∀ i ∈ List.range 1,StrictCheckAt 9 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 45) 9 45:=by decide +kernel
  have hfast:StrictAtFast (row 9 45) 9 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 45) 9 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 45) 9 45 hvalid hfast

theorem sr9p46:∀ i ∈ List.range 1,StrictCheckAt 9 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 46) 9 46:=by decide +kernel
  have hfast:StrictAtFast (row 9 46) 9 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 46) 9 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 46) 9 46 hvalid hfast

theorem sr9p47:∀ i ∈ List.range 1,StrictCheckAt 9 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 47) 9 47:=by decide +kernel
  have hfast:StrictAtFast (row 9 47) 9 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 47) 9 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 47) 9 47 hvalid hfast

theorem sr9p48:∀ i ∈ List.range 1,StrictCheckAt 9 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 48) 9 48:=by decide +kernel
  have hfast:StrictAtFast (row 9 48) 9 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 48) 9 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 48) 9 48 hvalid hfast

theorem sr9p49:∀ i ∈ List.range 1,StrictCheckAt 9 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 49) 9 49:=by decide +kernel
  have hfast:StrictAtFast (row 9 49) 9 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 49) 9 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 49) 9 49 hvalid hfast

theorem sr9p50:∀ i ∈ List.range 1,StrictCheckAt 9 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 50) 9 50:=by decide +kernel
  have hfast:StrictAtFast (row 9 50) 9 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 50) 9 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 50) 9 50 hvalid hfast

theorem sr9p51:∀ i ∈ List.range 1,StrictCheckAt 9 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 51) 9 51:=by decide +kernel
  have hfast:StrictAtFast (row 9 51) 9 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 51) 9 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 51) 9 51 hvalid hfast

theorem sr9p52:∀ i ∈ List.range 1,StrictCheckAt 9 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 52) 9 52:=by decide +kernel
  have hfast:StrictAtFast (row 9 52) 9 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 52) 9 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 52) 9 52 hvalid hfast

theorem sr9p53:∀ i ∈ List.range 1,StrictCheckAt 9 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 53) 9 53:=by decide +kernel
  have hfast:StrictAtFast (row 9 53) 9 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 53) 9 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 53) 9 53 hvalid hfast

theorem sr9p54:∀ i ∈ List.range 1,StrictCheckAt 9 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 54) 9 54:=by decide +kernel
  have hfast:StrictAtFast (row 9 54) 9 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 54) 9 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 54) 9 54 hvalid hfast

theorem sr9p55:∀ i ∈ List.range 1,StrictCheckAt 9 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 55) 9 55:=by decide +kernel
  have hfast:StrictAtFast (row 9 55) 9 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 55) 9 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 55) 9 55 hvalid hfast

theorem sr9p56:∀ i ∈ List.range 1,StrictCheckAt 9 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 56) 9 56:=by decide +kernel
  have hfast:StrictAtFast (row 9 56) 9 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 56) 9 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 56) 9 56 hvalid hfast

theorem sr9p57:∀ i ∈ List.range 1,StrictCheckAt 9 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 57) 9 57:=by decide +kernel
  have hfast:StrictAtFast (row 9 57) 9 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 57) 9 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 57) 9 57 hvalid hfast

theorem sr9p58:∀ i ∈ List.range 1,StrictCheckAt 9 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 58) 9 58:=by decide +kernel
  have hfast:StrictAtFast (row 9 58) 9 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 58) 9 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 58) 9 58 hvalid hfast

theorem sr9p59:∀ i ∈ List.range 1,StrictCheckAt 9 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 59) 9 59:=by decide +kernel
  have hfast:StrictAtFast (row 9 59) 9 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 59) 9 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 59) 9 59 hvalid hfast

theorem sr9p60:∀ i ∈ List.range 1,StrictCheckAt 9 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 60) 9 60:=by decide +kernel
  have hfast:StrictAtFast (row 9 60) 9 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 60) 9 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 60) 9 60 hvalid hfast

theorem sr9p61:∀ i ∈ List.range 1,StrictCheckAt 9 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 61) 9 61:=by decide +kernel
  have hfast:StrictAtFast (row 9 61) 9 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 61) 9 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 61) 9 61 hvalid hfast

theorem sr9p62:∀ i ∈ List.range 1,StrictCheckAt 9 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 62) 9 62:=by decide +kernel
  have hfast:StrictAtFast (row 9 62) 9 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 62) 9 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 62) 9 62 hvalid hfast

theorem sr9p63:∀ i ∈ List.range 1,StrictCheckAt 9 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 63) 9 63:=by decide +kernel
  have hfast:StrictAtFast (row 9 63) 9 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 63) 9 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 63) 9 63 hvalid hfast

theorem sr9p64:∀ i ∈ List.range 1,StrictCheckAt 9 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 64) 9 64:=by decide +kernel
  have hfast:StrictAtFast (row 9 64) 9 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 64) 9 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 64) 9 64 hvalid hfast

theorem sr9p65:∀ i ∈ List.range 1,StrictCheckAt 9 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 65) 9 65:=by decide +kernel
  have hfast:StrictAtFast (row 9 65) 9 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 65) 9 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 65) 9 65 hvalid hfast

theorem sr9p66:∀ i ∈ List.range 1,StrictCheckAt 9 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 66) 9 66:=by decide +kernel
  have hfast:StrictAtFast (row 9 66) 9 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 66) 9 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 66) 9 66 hvalid hfast

theorem sr9p67:∀ i ∈ List.range 1,StrictCheckAt 9 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 67) 9 67:=by decide +kernel
  have hfast:StrictAtFast (row 9 67) 9 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 67) 9 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 67) 9 67 hvalid hfast

theorem sr9p68:∀ i ∈ List.range 1,StrictCheckAt 9 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 68) 9 68:=by decide +kernel
  have hfast:StrictAtFast (row 9 68) 9 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 68) 9 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 68) 9 68 hvalid hfast

theorem sr9p69:∀ i ∈ List.range 1,StrictCheckAt 9 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 69) 9 69:=by decide +kernel
  have hfast:StrictAtFast (row 9 69) 9 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 69) 9 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 69) 9 69 hvalid hfast

theorem sr9p70:∀ i ∈ List.range 1,StrictCheckAt 9 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 70) 9 70:=by decide +kernel
  have hfast:StrictAtFast (row 9 70) 9 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 70) 9 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 70) 9 70 hvalid hfast

theorem sr9p71:∀ i ∈ List.range 1,StrictCheckAt 9 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 71) 9 71:=by decide +kernel
  have hfast:StrictAtFast (row 9 71) 9 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 71) 9 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 71) 9 71 hvalid hfast

theorem sr9p72:∀ i ∈ List.range 1,StrictCheckAt 9 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 72) 9 72:=by decide +kernel
  have hfast:StrictAtFast (row 9 72) 9 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 72) 9 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 72) 9 72 hvalid hfast

theorem sr9p73:∀ i ∈ List.range 1,StrictCheckAt 9 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 73) 9 73:=by decide +kernel
  have hfast:StrictAtFast (row 9 73) 9 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 73) 9 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 73) 9 73 hvalid hfast

theorem sr9p74:∀ i ∈ List.range 1,StrictCheckAt 9 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 74) 9 74:=by decide +kernel
  have hfast:StrictAtFast (row 9 74) 9 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 74) 9 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 74) 9 74 hvalid hfast

theorem sr9p75:∀ i ∈ List.range 1,StrictCheckAt 9 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 75) 9 75:=by decide +kernel
  have hfast:StrictAtFast (row 9 75) 9 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 75) 9 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 75) 9 75 hvalid hfast

theorem sr9p76:∀ i ∈ List.range 1,StrictCheckAt 9 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 76) 9 76:=by decide +kernel
  have hfast:StrictAtFast (row 9 76) 9 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 76) 9 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 76) 9 76 hvalid hfast

theorem sr9p77:∀ i ∈ List.range 1,StrictCheckAt 9 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 77) 9 77:=by decide +kernel
  have hfast:StrictAtFast (row 9 77) 9 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 77) 9 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 77) 9 77 hvalid hfast

theorem sr9p78:∀ i ∈ List.range 1,StrictCheckAt 9 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 78) 9 78:=by decide +kernel
  have hfast:StrictAtFast (row 9 78) 9 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 78) 9 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 78) 9 78 hvalid hfast

theorem sr9p79:∀ i ∈ List.range 1,StrictCheckAt 9 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 79) 9 79:=by decide +kernel
  have hfast:StrictAtFast (row 9 79) 9 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 79) 9 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 79) 9 79 hvalid hfast

theorem sr9p80:∀ i ∈ List.range 1,StrictCheckAt 9 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 80) 9 80:=by decide +kernel
  have hfast:StrictAtFast (row 9 80) 9 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 80) 9 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 80) 9 80 hvalid hfast

theorem sr9p81:∀ i ∈ List.range 1,StrictCheckAt 9 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 81) 9 81:=by decide +kernel
  have hfast:StrictAtFast (row 9 81) 9 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 81) 9 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 81) 9 81 hvalid hfast

theorem sr9p82:∀ i ∈ List.range 1,StrictCheckAt 9 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 82) 9 82:=by decide +kernel
  have hfast:StrictAtFast (row 9 82) 9 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 82) 9 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 82) 9 82 hvalid hfast

theorem sr9p83:∀ i ∈ List.range 1,StrictCheckAt 9 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 83) 9 83:=by decide +kernel
  have hfast:StrictAtFast (row 9 83) 9 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 83) 9 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 83) 9 83 hvalid hfast

theorem sr9p84:∀ i ∈ List.range 1,StrictCheckAt 9 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 84) 9 84:=by decide +kernel
  have hfast:StrictAtFast (row 9 84) 9 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 84) 9 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 84) 9 84 hvalid hfast

theorem sr9p85:∀ i ∈ List.range 1,StrictCheckAt 9 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 85) 9 85:=by decide +kernel
  have hfast:StrictAtFast (row 9 85) 9 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 85) 9 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 85) 9 85 hvalid hfast

theorem sr9p86:∀ i ∈ List.range 1,StrictCheckAt 9 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 86) 9 86:=by decide +kernel
  have hfast:StrictAtFast (row 9 86) 9 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 86) 9 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 86) 9 86 hvalid hfast

theorem sr9p87:∀ i ∈ List.range 1,StrictCheckAt 9 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 87) 9 87:=by decide +kernel
  have hfast:StrictAtFast (row 9 87) 9 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 87) 9 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 87) 9 87 hvalid hfast

theorem sr9p88:∀ i ∈ List.range 1,StrictCheckAt 9 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 88) 9 88:=by decide +kernel
  have hfast:StrictAtFast (row 9 88) 9 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 88) 9 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 88) 9 88 hvalid hfast

theorem sr9p89:∀ i ∈ List.range 1,StrictCheckAt 9 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 89) 9 89:=by decide +kernel
  have hfast:StrictAtFast (row 9 89) 9 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 89) 9 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 89) 9 89 hvalid hfast

theorem sr9p90:∀ i ∈ List.range 1,StrictCheckAt 9 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 90) 9 90:=by decide +kernel
  have hfast:StrictAtFast (row 9 90) 9 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 90) 9 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 90) 9 90 hvalid hfast

theorem sr9p91:∀ i ∈ List.range 1,StrictCheckAt 9 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 91) 9 91:=by decide +kernel
  have hfast:StrictAtFast (row 9 91) 9 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 91) 9 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 91) 9 91 hvalid hfast

theorem sr9p92:∀ i ∈ List.range 1,StrictCheckAt 9 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 92) 9 92:=by decide +kernel
  have hfast:StrictAtFast (row 9 92) 9 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 92) 9 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 92) 9 92 hvalid hfast

theorem sr9p93:∀ i ∈ List.range 1,StrictCheckAt 9 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 93) 9 93:=by decide +kernel
  have hfast:StrictAtFast (row 9 93) 9 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 93) 9 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 93) 9 93 hvalid hfast

theorem sr9p94:∀ i ∈ List.range 1,StrictCheckAt 9 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 94) 9 94:=by decide +kernel
  have hfast:StrictAtFast (row 9 94) 9 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 94) 9 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 94) 9 94 hvalid hfast

theorem sr9p95:∀ i ∈ List.range 1,StrictCheckAt 9 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 95) 9 95:=by decide +kernel
  have hfast:StrictAtFast (row 9 95) 9 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 95) 9 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 95) 9 95 hvalid hfast

theorem sr9p96:∀ i ∈ List.range 1,StrictCheckAt 9 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 96) 9 96:=by decide +kernel
  have hfast:StrictAtFast (row 9 96) 9 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 96) 9 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 96) 9 96 hvalid hfast

theorem sr9p97:∀ i ∈ List.range 1,StrictCheckAt 9 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 97) 9 97:=by decide +kernel
  have hfast:StrictAtFast (row 9 97) 9 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 97) 9 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 97) 9 97 hvalid hfast

theorem sr9p98:∀ i ∈ List.range 1,StrictCheckAt 9 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 98) 9 98:=by decide +kernel
  have hfast:StrictAtFast (row 9 98) 9 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 98) 9 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 98) 9 98 hvalid hfast

theorem sr9p99:∀ i ∈ List.range 1,StrictCheckAt 9 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 99) 9 99:=by decide +kernel
  have hfast:StrictAtFast (row 9 99) 9 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 99) 9 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 99) 9 99 hvalid hfast

theorem sr9p100:∀ i ∈ List.range 1,StrictCheckAt 9 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 100) 9 100:=by decide +kernel
  have hfast:StrictAtFast (row 9 100) 9 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 100) 9 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 100) 9 100 hvalid hfast

theorem sr9p101:∀ i ∈ List.range 1,StrictCheckAt 9 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 101) 9 101:=by decide +kernel
  have hfast:StrictAtFast (row 9 101) 9 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 101) 9 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 101) 9 101 hvalid hfast

theorem sr9p102:∀ i ∈ List.range 1,StrictCheckAt 9 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 102) 9 102:=by decide +kernel
  have hfast:StrictAtFast (row 9 102) 9 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 102) 9 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 102) 9 102 hvalid hfast

theorem sr9p103:∀ i ∈ List.range 1,StrictCheckAt 9 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 103) 9 103:=by decide +kernel
  have hfast:StrictAtFast (row 9 103) 9 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 103) 9 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 103) 9 103 hvalid hfast

theorem sr9p104:∀ i ∈ List.range 1,StrictCheckAt 9 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 104) 9 104:=by decide +kernel
  have hfast:StrictAtFast (row 9 104) 9 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 104) 9 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 104) 9 104 hvalid hfast

theorem sr9p105:∀ i ∈ List.range 1,StrictCheckAt 9 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 105) 9 105:=by decide +kernel
  have hfast:StrictAtFast (row 9 105) 9 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 105) 9 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 105) 9 105 hvalid hfast

theorem sr9p106:∀ i ∈ List.range 1,StrictCheckAt 9 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 106) 9 106:=by decide +kernel
  have hfast:StrictAtFast (row 9 106) 9 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 106) 9 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 106) 9 106 hvalid hfast

theorem sr9p107:∀ i ∈ List.range 1,StrictCheckAt 9 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 107) 9 107:=by decide +kernel
  have hfast:StrictAtFast (row 9 107) 9 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 107) 9 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 107) 9 107 hvalid hfast

theorem sr9p108:∀ i ∈ List.range 1,StrictCheckAt 9 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 108) 9 108:=by decide +kernel
  have hfast:StrictAtFast (row 9 108) 9 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 108) 9 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 108) 9 108 hvalid hfast

theorem sr9p109:∀ i ∈ List.range 1,StrictCheckAt 9 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 109) 9 109:=by decide +kernel
  have hfast:StrictAtFast (row 9 109) 9 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 109) 9 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 109) 9 109 hvalid hfast

theorem sr9p110:∀ i ∈ List.range 1,StrictCheckAt 9 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 110) 9 110:=by decide +kernel
  have hfast:StrictAtFast (row 9 110) 9 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 110) 9 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 110) 9 110 hvalid hfast

theorem sr9p111:∀ i ∈ List.range 1,StrictCheckAt 9 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 111) 9 111:=by decide +kernel
  have hfast:StrictAtFast (row 9 111) 9 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 111) 9 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 111) 9 111 hvalid hfast

theorem sr9p112:∀ i ∈ List.range 1,StrictCheckAt 9 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 112) 9 112:=by decide +kernel
  have hfast:StrictAtFast (row 9 112) 9 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 112) 9 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 112) 9 112 hvalid hfast

theorem sr9p113:∀ i ∈ List.range 1,StrictCheckAt 9 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 113) 9 113:=by decide +kernel
  have hfast:StrictAtFast (row 9 113) 9 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 113) 9 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 113) 9 113 hvalid hfast

theorem sr9p114:∀ i ∈ List.range 1,StrictCheckAt 9 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 114) 9 114:=by decide +kernel
  have hfast:StrictAtFast (row 9 114) 9 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 114) 9 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 114) 9 114 hvalid hfast

theorem sr9p115:∀ i ∈ List.range 1,StrictCheckAt 9 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 115) 9 115:=by decide +kernel
  have hfast:StrictAtFast (row 9 115) 9 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 115) 9 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 115) 9 115 hvalid hfast

theorem sr9p116:∀ i ∈ List.range 1,StrictCheckAt 9 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 116) 9 116:=by decide +kernel
  have hfast:StrictAtFast (row 9 116) 9 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 116) 9 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 116) 9 116 hvalid hfast

theorem sr9p117:∀ i ∈ List.range 1,StrictCheckAt 9 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 117) 9 117:=by decide +kernel
  have hfast:StrictAtFast (row 9 117) 9 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 117) 9 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 117) 9 117 hvalid hfast

theorem sr9p118:∀ i ∈ List.range 1,StrictCheckAt 9 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 118) 9 118:=by decide +kernel
  have hfast:StrictAtFast (row 9 118) 9 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 118) 9 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 118) 9 118 hvalid hfast

theorem sr9p119:∀ i ∈ List.range 1,StrictCheckAt 9 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 119) 9 119:=by decide +kernel
  have hfast:StrictAtFast (row 9 119) 9 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 119) 9 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 119) 9 119 hvalid hfast

theorem sr9p120:∀ i ∈ List.range 1,StrictCheckAt 9 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 120) 9 120:=by decide +kernel
  have hfast:StrictAtFast (row 9 120) 9 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 120) 9 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 120) 9 120 hvalid hfast

theorem sr9p121:∀ i ∈ List.range 1,StrictCheckAt 9 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 121) 9 121:=by decide +kernel
  have hfast:StrictAtFast (row 9 121) 9 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 121) 9 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 121) 9 121 hvalid hfast

theorem sr9p122:∀ i ∈ List.range 1,StrictCheckAt 9 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 122) 9 122:=by decide +kernel
  have hfast:StrictAtFast (row 9 122) 9 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 122) 9 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 122) 9 122 hvalid hfast

theorem sr9p123:∀ i ∈ List.range 1,StrictCheckAt 9 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 123) 9 123:=by decide +kernel
  have hfast:StrictAtFast (row 9 123) 9 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 123) 9 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 123) 9 123 hvalid hfast

theorem sr9p124:∀ i ∈ List.range 1,StrictCheckAt 9 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 124) 9 124:=by decide +kernel
  have hfast:StrictAtFast (row 9 124) 9 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 124) 9 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 124) 9 124 hvalid hfast

theorem sr9p125:∀ i ∈ List.range 1,StrictCheckAt 9 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 125) 9 125:=by decide +kernel
  have hfast:StrictAtFast (row 9 125) 9 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 125) 9 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 125) 9 125 hvalid hfast

theorem sr9p126:∀ i ∈ List.range 1,StrictCheckAt 9 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 126) 9 126:=by decide +kernel
  have hfast:StrictAtFast (row 9 126) 9 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 126) 9 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 126) 9 126 hvalid hfast

theorem sr9p127:∀ i ∈ List.range 1,StrictCheckAt 9 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 127) 9 127:=by decide +kernel
  have hfast:StrictAtFast (row 9 127) 9 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 127) 9 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 127) 9 127 hvalid hfast

theorem sr9p128:∀ i ∈ List.range 1,StrictCheckAt 9 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 128) 9 128:=by decide +kernel
  have hfast:StrictAtFast (row 9 128) 9 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 128) 9 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 128) 9 128 hvalid hfast

theorem sr9p129:∀ i ∈ List.range 1,StrictCheckAt 9 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 129) 9 129:=by decide +kernel
  have hfast:StrictAtFast (row 9 129) 9 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 129) 9 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 129) 9 129 hvalid hfast

theorem sr9p130:∀ i ∈ List.range 1,StrictCheckAt 9 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 130) 9 130:=by decide +kernel
  have hfast:StrictAtFast (row 9 130) 9 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 130) 9 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 130) 9 130 hvalid hfast

theorem sr9p131:∀ i ∈ List.range 1,StrictCheckAt 9 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 131 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 131) 9 131:=by decide +kernel
  have hfast:StrictAtFast (row 9 131) 9 131:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 131) 9 131 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 131) 9 131 hvalid hfast

theorem sr9p132:∀ i ∈ List.range 1,StrictCheckAt 9 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 132 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 132) 9 132:=by decide +kernel
  have hfast:StrictAtFast (row 9 132) 9 132:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 132) 9 132 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 132) 9 132 hvalid hfast

theorem sr9p133:∀ i ∈ List.range 1,StrictCheckAt 9 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 9 133 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 9 133) 9 133:=by decide +kernel
  have hfast:StrictAtFast (row 9 133) 9 133:=
    BoundaryTailStrictConvex.endpoints_sound (row 9 133) 9 133 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 9 133) 9 133 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
