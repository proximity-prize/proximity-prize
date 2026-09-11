import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr10p0:∀ i ∈ List.range 8,CorrectAt 10 (0+i):=by decide +kernel

theorem cr10p1:∀ i ∈ List.range 8,CorrectAt 10 (8+i):=by decide +kernel

theorem cr10p2:∀ i ∈ List.range 8,CorrectAt 10 (16+i):=by decide +kernel

theorem cr10p3:∀ i ∈ List.range 8,CorrectAt 10 (24+i):=by decide +kernel

theorem cr10p4:∀ i ∈ List.range 8,CorrectAt 10 (32+i):=by decide +kernel

theorem cr10p5:∀ i ∈ List.range 8,CorrectAt 10 (40+i):=by decide +kernel

theorem cr10p6:∀ i ∈ List.range 8,CorrectAt 10 (48+i):=by decide +kernel

theorem cr10p7:∀ i ∈ List.range 8,CorrectAt 10 (56+i):=by decide +kernel

theorem cr10p8:∀ i ∈ List.range 8,CorrectAt 10 (64+i):=by decide +kernel

theorem cr10p9:∀ i ∈ List.range 8,CorrectAt 10 (72+i):=by decide +kernel

theorem cr10p10:∀ i ∈ List.range 8,CorrectAt 10 (80+i):=by decide +kernel

theorem cr10p11:∀ i ∈ List.range 8,CorrectAt 10 (88+i):=by decide +kernel

theorem cr10p12:∀ i ∈ List.range 8,CorrectAt 10 (96+i):=by decide +kernel

theorem cr10p13:∀ i ∈ List.range 8,CorrectAt 10 (104+i):=by decide +kernel

theorem cr10p14:∀ i ∈ List.range 8,CorrectAt 10 (112+i):=by decide +kernel

theorem cr10p15:∀ i ∈ List.range 8,CorrectAt 10 (120+i):=by decide +kernel

theorem cr10p16:∀ i ∈ List.range 5,CorrectAt 10 (128+i):=by decide +kernel

theorem sr10p0:∀ i ∈ List.range 1,StrictCheckAt 10 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 0) 10 0:=by decide +kernel
  have hfast:StrictAtFast (row 10 0) 10 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 0) 10 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 0) 10 0 hvalid hfast

theorem sr10p1:∀ i ∈ List.range 1,StrictCheckAt 10 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 1) 10 1:=by decide +kernel
  have hfast:StrictAtFast (row 10 1) 10 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 1) 10 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 1) 10 1 hvalid hfast

theorem sr10p2:∀ i ∈ List.range 1,StrictCheckAt 10 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 2) 10 2:=by decide +kernel
  have hfast:StrictAtFast (row 10 2) 10 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 2) 10 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 2) 10 2 hvalid hfast

theorem sr10p3:∀ i ∈ List.range 1,StrictCheckAt 10 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 3) 10 3:=by decide +kernel
  have hfast:StrictAtFast (row 10 3) 10 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 3) 10 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 3) 10 3 hvalid hfast

theorem sr10p4:∀ i ∈ List.range 1,StrictCheckAt 10 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 4) 10 4:=by decide +kernel
  have hfast:StrictAtFast (row 10 4) 10 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 4) 10 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 4) 10 4 hvalid hfast

theorem sr10p5:∀ i ∈ List.range 1,StrictCheckAt 10 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 5) 10 5:=by decide +kernel
  have hfast:StrictAtFast (row 10 5) 10 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 5) 10 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 5) 10 5 hvalid hfast

theorem sr10p6:∀ i ∈ List.range 1,StrictCheckAt 10 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 6) 10 6:=by decide +kernel
  have hfast:StrictAtFast (row 10 6) 10 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 6) 10 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 6) 10 6 hvalid hfast

theorem sr10p7:∀ i ∈ List.range 1,StrictCheckAt 10 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 7) 10 7:=by decide +kernel
  have hfast:StrictAtFast (row 10 7) 10 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 7) 10 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 7) 10 7 hvalid hfast

theorem sr10p8:∀ i ∈ List.range 1,StrictCheckAt 10 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 8) 10 8:=by decide +kernel
  have hfast:StrictAtFast (row 10 8) 10 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 8) 10 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 8) 10 8 hvalid hfast

theorem sr10p9:∀ i ∈ List.range 1,StrictCheckAt 10 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 9) 10 9:=by decide +kernel
  have hfast:StrictAtFast (row 10 9) 10 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 9) 10 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 9) 10 9 hvalid hfast

theorem sr10p10:∀ i ∈ List.range 1,StrictCheckAt 10 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 10) 10 10:=by decide +kernel
  have hfast:StrictAtFast (row 10 10) 10 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 10) 10 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 10) 10 10 hvalid hfast

theorem sr10p11:∀ i ∈ List.range 1,StrictCheckAt 10 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 11) 10 11:=by decide +kernel
  have hfast:StrictAtFast (row 10 11) 10 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 11) 10 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 11) 10 11 hvalid hfast

theorem sr10p12:∀ i ∈ List.range 1,StrictCheckAt 10 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 12) 10 12:=by decide +kernel
  have hfast:StrictAtFast (row 10 12) 10 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 12) 10 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 12) 10 12 hvalid hfast

theorem sr10p13:∀ i ∈ List.range 1,StrictCheckAt 10 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 13) 10 13:=by decide +kernel
  have hfast:StrictAtFast (row 10 13) 10 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 13) 10 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 13) 10 13 hvalid hfast

theorem sr10p14:∀ i ∈ List.range 1,StrictCheckAt 10 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 14) 10 14:=by decide +kernel
  have hfast:StrictAtFast (row 10 14) 10 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 14) 10 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 14) 10 14 hvalid hfast

theorem sr10p15:∀ i ∈ List.range 1,StrictCheckAt 10 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 15) 10 15:=by decide +kernel
  have hfast:StrictAtFast (row 10 15) 10 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 15) 10 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 15) 10 15 hvalid hfast

theorem sr10p16:∀ i ∈ List.range 1,StrictCheckAt 10 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 16) 10 16:=by decide +kernel
  have hfast:StrictAtFast (row 10 16) 10 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 16) 10 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 16) 10 16 hvalid hfast

theorem sr10p17:∀ i ∈ List.range 1,StrictCheckAt 10 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 17) 10 17:=by decide +kernel
  have hfast:StrictAtFast (row 10 17) 10 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 17) 10 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 17) 10 17 hvalid hfast

theorem sr10p18:∀ i ∈ List.range 1,StrictCheckAt 10 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 18) 10 18:=by decide +kernel
  have hfast:StrictAtFast (row 10 18) 10 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 18) 10 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 18) 10 18 hvalid hfast

theorem sr10p19:∀ i ∈ List.range 1,StrictCheckAt 10 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 19) 10 19:=by decide +kernel
  have hfast:StrictAtFast (row 10 19) 10 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 19) 10 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 19) 10 19 hvalid hfast

theorem sr10p20:∀ i ∈ List.range 1,StrictCheckAt 10 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 20) 10 20:=by decide +kernel
  have hfast:StrictAtFast (row 10 20) 10 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 20) 10 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 20) 10 20 hvalid hfast

theorem sr10p21:∀ i ∈ List.range 1,StrictCheckAt 10 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 21) 10 21:=by decide +kernel
  have hfast:StrictAtFast (row 10 21) 10 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 21) 10 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 21) 10 21 hvalid hfast

theorem sr10p22:∀ i ∈ List.range 1,StrictCheckAt 10 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 22) 10 22:=by decide +kernel
  have hfast:StrictAtFast (row 10 22) 10 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 22) 10 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 22) 10 22 hvalid hfast

theorem sr10p23:∀ i ∈ List.range 1,StrictCheckAt 10 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 23) 10 23:=by decide +kernel
  have hfast:StrictAtFast (row 10 23) 10 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 23) 10 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 23) 10 23 hvalid hfast

theorem sr10p24:∀ i ∈ List.range 1,StrictCheckAt 10 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 24) 10 24:=by decide +kernel
  have hfast:StrictAtFast (row 10 24) 10 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 24) 10 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 24) 10 24 hvalid hfast

theorem sr10p25:∀ i ∈ List.range 1,StrictCheckAt 10 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 25) 10 25:=by decide +kernel
  have hfast:StrictAtFast (row 10 25) 10 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 25) 10 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 25) 10 25 hvalid hfast

theorem sr10p26:∀ i ∈ List.range 1,StrictCheckAt 10 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 26) 10 26:=by decide +kernel
  have hfast:StrictAtFast (row 10 26) 10 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 26) 10 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 26) 10 26 hvalid hfast

theorem sr10p27:∀ i ∈ List.range 1,StrictCheckAt 10 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 27) 10 27:=by decide +kernel
  have hfast:StrictAtFast (row 10 27) 10 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 27) 10 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 27) 10 27 hvalid hfast

theorem sr10p28:∀ i ∈ List.range 1,StrictCheckAt 10 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 28) 10 28:=by decide +kernel
  have hfast:StrictAtFast (row 10 28) 10 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 28) 10 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 28) 10 28 hvalid hfast

theorem sr10p29:∀ i ∈ List.range 1,StrictCheckAt 10 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 29) 10 29:=by decide +kernel
  have hfast:StrictAtFast (row 10 29) 10 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 29) 10 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 29) 10 29 hvalid hfast

theorem sr10p30:∀ i ∈ List.range 1,StrictCheckAt 10 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 30) 10 30:=by decide +kernel
  have hfast:StrictAtFast (row 10 30) 10 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 30) 10 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 30) 10 30 hvalid hfast

theorem sr10p31:∀ i ∈ List.range 1,StrictCheckAt 10 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 31) 10 31:=by decide +kernel
  have hfast:StrictAtFast (row 10 31) 10 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 31) 10 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 31) 10 31 hvalid hfast

theorem sr10p32:∀ i ∈ List.range 1,StrictCheckAt 10 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 32) 10 32:=by decide +kernel
  have hfast:StrictAtFast (row 10 32) 10 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 32) 10 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 32) 10 32 hvalid hfast

theorem sr10p33:∀ i ∈ List.range 1,StrictCheckAt 10 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 33) 10 33:=by decide +kernel
  have hfast:StrictAtFast (row 10 33) 10 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 33) 10 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 33) 10 33 hvalid hfast

theorem sr10p34:∀ i ∈ List.range 1,StrictCheckAt 10 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 34) 10 34:=by decide +kernel
  have hfast:StrictAtFast (row 10 34) 10 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 34) 10 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 34) 10 34 hvalid hfast

theorem sr10p35:∀ i ∈ List.range 1,StrictCheckAt 10 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 35) 10 35:=by decide +kernel
  have hfast:StrictAtFast (row 10 35) 10 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 35) 10 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 35) 10 35 hvalid hfast

theorem sr10p36:∀ i ∈ List.range 1,StrictCheckAt 10 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 36) 10 36:=by decide +kernel
  have hfast:StrictAtFast (row 10 36) 10 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 36) 10 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 36) 10 36 hvalid hfast

theorem sr10p37:∀ i ∈ List.range 1,StrictCheckAt 10 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 37) 10 37:=by decide +kernel
  have hfast:StrictAtFast (row 10 37) 10 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 37) 10 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 37) 10 37 hvalid hfast

theorem sr10p38:∀ i ∈ List.range 1,StrictCheckAt 10 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 38) 10 38:=by decide +kernel
  have hfast:StrictAtFast (row 10 38) 10 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 38) 10 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 38) 10 38 hvalid hfast

theorem sr10p39:∀ i ∈ List.range 1,StrictCheckAt 10 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 39) 10 39:=by decide +kernel
  have hfast:StrictAtFast (row 10 39) 10 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 39) 10 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 39) 10 39 hvalid hfast

theorem sr10p40:∀ i ∈ List.range 1,StrictCheckAt 10 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 40) 10 40:=by decide +kernel
  have hfast:StrictAtFast (row 10 40) 10 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 40) 10 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 40) 10 40 hvalid hfast

theorem sr10p41:∀ i ∈ List.range 1,StrictCheckAt 10 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 41) 10 41:=by decide +kernel
  have hfast:StrictAtFast (row 10 41) 10 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 41) 10 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 41) 10 41 hvalid hfast

theorem sr10p42:∀ i ∈ List.range 1,StrictCheckAt 10 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 42) 10 42:=by decide +kernel
  have hfast:StrictAtFast (row 10 42) 10 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 42) 10 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 42) 10 42 hvalid hfast

theorem sr10p43:∀ i ∈ List.range 1,StrictCheckAt 10 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 43) 10 43:=by decide +kernel
  have hfast:StrictAtFast (row 10 43) 10 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 43) 10 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 43) 10 43 hvalid hfast

theorem sr10p44:∀ i ∈ List.range 1,StrictCheckAt 10 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 44) 10 44:=by decide +kernel
  have hfast:StrictAtFast (row 10 44) 10 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 44) 10 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 44) 10 44 hvalid hfast

theorem sr10p45:∀ i ∈ List.range 1,StrictCheckAt 10 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 45) 10 45:=by decide +kernel
  have hfast:StrictAtFast (row 10 45) 10 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 45) 10 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 45) 10 45 hvalid hfast

theorem sr10p46:∀ i ∈ List.range 1,StrictCheckAt 10 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 46) 10 46:=by decide +kernel
  have hfast:StrictAtFast (row 10 46) 10 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 46) 10 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 46) 10 46 hvalid hfast

theorem sr10p47:∀ i ∈ List.range 1,StrictCheckAt 10 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 47) 10 47:=by decide +kernel
  have hfast:StrictAtFast (row 10 47) 10 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 47) 10 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 47) 10 47 hvalid hfast

theorem sr10p48:∀ i ∈ List.range 1,StrictCheckAt 10 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 48) 10 48:=by decide +kernel
  have hfast:StrictAtFast (row 10 48) 10 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 48) 10 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 48) 10 48 hvalid hfast

theorem sr10p49:∀ i ∈ List.range 1,StrictCheckAt 10 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 49) 10 49:=by decide +kernel
  have hfast:StrictAtFast (row 10 49) 10 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 49) 10 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 49) 10 49 hvalid hfast

theorem sr10p50:∀ i ∈ List.range 1,StrictCheckAt 10 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 50) 10 50:=by decide +kernel
  have hfast:StrictAtFast (row 10 50) 10 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 50) 10 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 50) 10 50 hvalid hfast

theorem sr10p51:∀ i ∈ List.range 1,StrictCheckAt 10 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 51) 10 51:=by decide +kernel
  have hfast:StrictAtFast (row 10 51) 10 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 51) 10 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 51) 10 51 hvalid hfast

theorem sr10p52:∀ i ∈ List.range 1,StrictCheckAt 10 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 52) 10 52:=by decide +kernel
  have hfast:StrictAtFast (row 10 52) 10 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 52) 10 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 52) 10 52 hvalid hfast

theorem sr10p53:∀ i ∈ List.range 1,StrictCheckAt 10 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 53) 10 53:=by decide +kernel
  have hfast:StrictAtFast (row 10 53) 10 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 53) 10 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 53) 10 53 hvalid hfast

theorem sr10p54:∀ i ∈ List.range 1,StrictCheckAt 10 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 54) 10 54:=by decide +kernel
  have hfast:StrictAtFast (row 10 54) 10 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 54) 10 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 54) 10 54 hvalid hfast

theorem sr10p55:∀ i ∈ List.range 1,StrictCheckAt 10 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 55) 10 55:=by decide +kernel
  have hfast:StrictAtFast (row 10 55) 10 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 55) 10 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 55) 10 55 hvalid hfast

theorem sr10p56:∀ i ∈ List.range 1,StrictCheckAt 10 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 56) 10 56:=by decide +kernel
  have hfast:StrictAtFast (row 10 56) 10 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 56) 10 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 56) 10 56 hvalid hfast

theorem sr10p57:∀ i ∈ List.range 1,StrictCheckAt 10 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 57) 10 57:=by decide +kernel
  have hfast:StrictAtFast (row 10 57) 10 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 57) 10 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 57) 10 57 hvalid hfast

theorem sr10p58:∀ i ∈ List.range 1,StrictCheckAt 10 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 58) 10 58:=by decide +kernel
  have hfast:StrictAtFast (row 10 58) 10 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 58) 10 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 58) 10 58 hvalid hfast

theorem sr10p59:∀ i ∈ List.range 1,StrictCheckAt 10 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 59) 10 59:=by decide +kernel
  have hfast:StrictAtFast (row 10 59) 10 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 59) 10 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 59) 10 59 hvalid hfast

theorem sr10p60:∀ i ∈ List.range 1,StrictCheckAt 10 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 60) 10 60:=by decide +kernel
  have hfast:StrictAtFast (row 10 60) 10 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 60) 10 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 60) 10 60 hvalid hfast

theorem sr10p61:∀ i ∈ List.range 1,StrictCheckAt 10 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 61) 10 61:=by decide +kernel
  have hfast:StrictAtFast (row 10 61) 10 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 61) 10 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 61) 10 61 hvalid hfast

theorem sr10p62:∀ i ∈ List.range 1,StrictCheckAt 10 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 62) 10 62:=by decide +kernel
  have hfast:StrictAtFast (row 10 62) 10 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 62) 10 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 62) 10 62 hvalid hfast

theorem sr10p63:∀ i ∈ List.range 1,StrictCheckAt 10 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 63) 10 63:=by decide +kernel
  have hfast:StrictAtFast (row 10 63) 10 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 63) 10 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 63) 10 63 hvalid hfast

theorem sr10p64:∀ i ∈ List.range 1,StrictCheckAt 10 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 64) 10 64:=by decide +kernel
  have hfast:StrictAtFast (row 10 64) 10 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 64) 10 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 64) 10 64 hvalid hfast

theorem sr10p65:∀ i ∈ List.range 1,StrictCheckAt 10 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 65) 10 65:=by decide +kernel
  have hfast:StrictAtFast (row 10 65) 10 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 65) 10 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 65) 10 65 hvalid hfast

theorem sr10p66:∀ i ∈ List.range 1,StrictCheckAt 10 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 66) 10 66:=by decide +kernel
  have hfast:StrictAtFast (row 10 66) 10 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 66) 10 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 66) 10 66 hvalid hfast

theorem sr10p67:∀ i ∈ List.range 1,StrictCheckAt 10 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 67) 10 67:=by decide +kernel
  have hfast:StrictAtFast (row 10 67) 10 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 67) 10 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 67) 10 67 hvalid hfast

theorem sr10p68:∀ i ∈ List.range 1,StrictCheckAt 10 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 68) 10 68:=by decide +kernel
  have hfast:StrictAtFast (row 10 68) 10 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 68) 10 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 68) 10 68 hvalid hfast

theorem sr10p69:∀ i ∈ List.range 1,StrictCheckAt 10 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 69) 10 69:=by decide +kernel
  have hfast:StrictAtFast (row 10 69) 10 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 69) 10 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 69) 10 69 hvalid hfast

theorem sr10p70:∀ i ∈ List.range 1,StrictCheckAt 10 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 70) 10 70:=by decide +kernel
  have hfast:StrictAtFast (row 10 70) 10 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 70) 10 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 70) 10 70 hvalid hfast

theorem sr10p71:∀ i ∈ List.range 1,StrictCheckAt 10 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 71) 10 71:=by decide +kernel
  have hfast:StrictAtFast (row 10 71) 10 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 71) 10 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 71) 10 71 hvalid hfast

theorem sr10p72:∀ i ∈ List.range 1,StrictCheckAt 10 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 72) 10 72:=by decide +kernel
  have hfast:StrictAtFast (row 10 72) 10 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 72) 10 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 72) 10 72 hvalid hfast

theorem sr10p73:∀ i ∈ List.range 1,StrictCheckAt 10 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 73) 10 73:=by decide +kernel
  have hfast:StrictAtFast (row 10 73) 10 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 73) 10 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 73) 10 73 hvalid hfast

theorem sr10p74:∀ i ∈ List.range 1,StrictCheckAt 10 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 74) 10 74:=by decide +kernel
  have hfast:StrictAtFast (row 10 74) 10 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 74) 10 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 74) 10 74 hvalid hfast

theorem sr10p75:∀ i ∈ List.range 1,StrictCheckAt 10 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 75) 10 75:=by decide +kernel
  have hfast:StrictAtFast (row 10 75) 10 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 75) 10 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 75) 10 75 hvalid hfast

theorem sr10p76:∀ i ∈ List.range 1,StrictCheckAt 10 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 76) 10 76:=by decide +kernel
  have hfast:StrictAtFast (row 10 76) 10 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 76) 10 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 76) 10 76 hvalid hfast

theorem sr10p77:∀ i ∈ List.range 1,StrictCheckAt 10 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 77) 10 77:=by decide +kernel
  have hfast:StrictAtFast (row 10 77) 10 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 77) 10 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 77) 10 77 hvalid hfast

theorem sr10p78:∀ i ∈ List.range 1,StrictCheckAt 10 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 78) 10 78:=by decide +kernel
  have hfast:StrictAtFast (row 10 78) 10 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 78) 10 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 78) 10 78 hvalid hfast

theorem sr10p79:∀ i ∈ List.range 1,StrictCheckAt 10 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 79) 10 79:=by decide +kernel
  have hfast:StrictAtFast (row 10 79) 10 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 79) 10 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 79) 10 79 hvalid hfast

theorem sr10p80:∀ i ∈ List.range 1,StrictCheckAt 10 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 80) 10 80:=by decide +kernel
  have hfast:StrictAtFast (row 10 80) 10 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 80) 10 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 80) 10 80 hvalid hfast

theorem sr10p81:∀ i ∈ List.range 1,StrictCheckAt 10 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 81) 10 81:=by decide +kernel
  have hfast:StrictAtFast (row 10 81) 10 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 81) 10 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 81) 10 81 hvalid hfast

theorem sr10p82:∀ i ∈ List.range 1,StrictCheckAt 10 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 82) 10 82:=by decide +kernel
  have hfast:StrictAtFast (row 10 82) 10 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 82) 10 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 82) 10 82 hvalid hfast

theorem sr10p83:∀ i ∈ List.range 1,StrictCheckAt 10 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 83) 10 83:=by decide +kernel
  have hfast:StrictAtFast (row 10 83) 10 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 83) 10 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 83) 10 83 hvalid hfast

theorem sr10p84:∀ i ∈ List.range 1,StrictCheckAt 10 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 84) 10 84:=by decide +kernel
  have hfast:StrictAtFast (row 10 84) 10 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 84) 10 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 84) 10 84 hvalid hfast

theorem sr10p85:∀ i ∈ List.range 1,StrictCheckAt 10 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 85) 10 85:=by decide +kernel
  have hfast:StrictAtFast (row 10 85) 10 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 85) 10 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 85) 10 85 hvalid hfast

theorem sr10p86:∀ i ∈ List.range 1,StrictCheckAt 10 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 86) 10 86:=by decide +kernel
  have hfast:StrictAtFast (row 10 86) 10 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 86) 10 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 86) 10 86 hvalid hfast

theorem sr10p87:∀ i ∈ List.range 1,StrictCheckAt 10 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 87) 10 87:=by decide +kernel
  have hfast:StrictAtFast (row 10 87) 10 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 87) 10 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 87) 10 87 hvalid hfast

theorem sr10p88:∀ i ∈ List.range 1,StrictCheckAt 10 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 88) 10 88:=by decide +kernel
  have hfast:StrictAtFast (row 10 88) 10 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 88) 10 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 88) 10 88 hvalid hfast

theorem sr10p89:∀ i ∈ List.range 1,StrictCheckAt 10 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 89) 10 89:=by decide +kernel
  have hfast:StrictAtFast (row 10 89) 10 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 89) 10 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 89) 10 89 hvalid hfast

theorem sr10p90:∀ i ∈ List.range 1,StrictCheckAt 10 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 90) 10 90:=by decide +kernel
  have hfast:StrictAtFast (row 10 90) 10 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 90) 10 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 90) 10 90 hvalid hfast

theorem sr10p91:∀ i ∈ List.range 1,StrictCheckAt 10 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 91) 10 91:=by decide +kernel
  have hfast:StrictAtFast (row 10 91) 10 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 91) 10 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 91) 10 91 hvalid hfast

theorem sr10p92:∀ i ∈ List.range 1,StrictCheckAt 10 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 92) 10 92:=by decide +kernel
  have hfast:StrictAtFast (row 10 92) 10 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 92) 10 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 92) 10 92 hvalid hfast

theorem sr10p93:∀ i ∈ List.range 1,StrictCheckAt 10 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 93) 10 93:=by decide +kernel
  have hfast:StrictAtFast (row 10 93) 10 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 93) 10 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 93) 10 93 hvalid hfast

theorem sr10p94:∀ i ∈ List.range 1,StrictCheckAt 10 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 94) 10 94:=by decide +kernel
  have hfast:StrictAtFast (row 10 94) 10 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 94) 10 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 94) 10 94 hvalid hfast

theorem sr10p95:∀ i ∈ List.range 1,StrictCheckAt 10 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 95) 10 95:=by decide +kernel
  have hfast:StrictAtFast (row 10 95) 10 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 95) 10 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 95) 10 95 hvalid hfast

theorem sr10p96:∀ i ∈ List.range 1,StrictCheckAt 10 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 96) 10 96:=by decide +kernel
  have hfast:StrictAtFast (row 10 96) 10 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 96) 10 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 96) 10 96 hvalid hfast

theorem sr10p97:∀ i ∈ List.range 1,StrictCheckAt 10 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 97) 10 97:=by decide +kernel
  have hfast:StrictAtFast (row 10 97) 10 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 97) 10 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 97) 10 97 hvalid hfast

theorem sr10p98:∀ i ∈ List.range 1,StrictCheckAt 10 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 98) 10 98:=by decide +kernel
  have hfast:StrictAtFast (row 10 98) 10 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 98) 10 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 98) 10 98 hvalid hfast

theorem sr10p99:∀ i ∈ List.range 1,StrictCheckAt 10 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 99) 10 99:=by decide +kernel
  have hfast:StrictAtFast (row 10 99) 10 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 99) 10 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 99) 10 99 hvalid hfast

theorem sr10p100:∀ i ∈ List.range 1,StrictCheckAt 10 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 100) 10 100:=by decide +kernel
  have hfast:StrictAtFast (row 10 100) 10 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 100) 10 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 100) 10 100 hvalid hfast

theorem sr10p101:∀ i ∈ List.range 1,StrictCheckAt 10 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 101) 10 101:=by decide +kernel
  have hfast:StrictAtFast (row 10 101) 10 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 101) 10 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 101) 10 101 hvalid hfast

theorem sr10p102:∀ i ∈ List.range 1,StrictCheckAt 10 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 102) 10 102:=by decide +kernel
  have hfast:StrictAtFast (row 10 102) 10 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 102) 10 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 102) 10 102 hvalid hfast

theorem sr10p103:∀ i ∈ List.range 1,StrictCheckAt 10 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 103) 10 103:=by decide +kernel
  have hfast:StrictAtFast (row 10 103) 10 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 103) 10 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 103) 10 103 hvalid hfast

theorem sr10p104:∀ i ∈ List.range 1,StrictCheckAt 10 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 104) 10 104:=by decide +kernel
  have hfast:StrictAtFast (row 10 104) 10 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 104) 10 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 104) 10 104 hvalid hfast

theorem sr10p105:∀ i ∈ List.range 1,StrictCheckAt 10 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 105) 10 105:=by decide +kernel
  have hfast:StrictAtFast (row 10 105) 10 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 105) 10 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 105) 10 105 hvalid hfast

theorem sr10p106:∀ i ∈ List.range 1,StrictCheckAt 10 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 106) 10 106:=by decide +kernel
  have hfast:StrictAtFast (row 10 106) 10 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 106) 10 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 106) 10 106 hvalid hfast

theorem sr10p107:∀ i ∈ List.range 1,StrictCheckAt 10 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 107) 10 107:=by decide +kernel
  have hfast:StrictAtFast (row 10 107) 10 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 107) 10 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 107) 10 107 hvalid hfast

theorem sr10p108:∀ i ∈ List.range 1,StrictCheckAt 10 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 108) 10 108:=by decide +kernel
  have hfast:StrictAtFast (row 10 108) 10 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 108) 10 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 108) 10 108 hvalid hfast

theorem sr10p109:∀ i ∈ List.range 1,StrictCheckAt 10 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 109) 10 109:=by decide +kernel
  have hfast:StrictAtFast (row 10 109) 10 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 109) 10 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 109) 10 109 hvalid hfast

theorem sr10p110:∀ i ∈ List.range 1,StrictCheckAt 10 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 110) 10 110:=by decide +kernel
  have hfast:StrictAtFast (row 10 110) 10 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 110) 10 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 110) 10 110 hvalid hfast

theorem sr10p111:∀ i ∈ List.range 1,StrictCheckAt 10 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 111) 10 111:=by decide +kernel
  have hfast:StrictAtFast (row 10 111) 10 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 111) 10 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 111) 10 111 hvalid hfast

theorem sr10p112:∀ i ∈ List.range 1,StrictCheckAt 10 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 112) 10 112:=by decide +kernel
  have hfast:StrictAtFast (row 10 112) 10 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 112) 10 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 112) 10 112 hvalid hfast

theorem sr10p113:∀ i ∈ List.range 1,StrictCheckAt 10 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 113) 10 113:=by decide +kernel
  have hfast:StrictAtFast (row 10 113) 10 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 113) 10 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 113) 10 113 hvalid hfast

theorem sr10p114:∀ i ∈ List.range 1,StrictCheckAt 10 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 114) 10 114:=by decide +kernel
  have hfast:StrictAtFast (row 10 114) 10 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 114) 10 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 114) 10 114 hvalid hfast

theorem sr10p115:∀ i ∈ List.range 1,StrictCheckAt 10 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 115) 10 115:=by decide +kernel
  have hfast:StrictAtFast (row 10 115) 10 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 115) 10 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 115) 10 115 hvalid hfast

theorem sr10p116:∀ i ∈ List.range 1,StrictCheckAt 10 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 116) 10 116:=by decide +kernel
  have hfast:StrictAtFast (row 10 116) 10 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 116) 10 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 116) 10 116 hvalid hfast

theorem sr10p117:∀ i ∈ List.range 1,StrictCheckAt 10 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 117) 10 117:=by decide +kernel
  have hfast:StrictAtFast (row 10 117) 10 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 117) 10 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 117) 10 117 hvalid hfast

theorem sr10p118:∀ i ∈ List.range 1,StrictCheckAt 10 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 118) 10 118:=by decide +kernel
  have hfast:StrictAtFast (row 10 118) 10 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 118) 10 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 118) 10 118 hvalid hfast

theorem sr10p119:∀ i ∈ List.range 1,StrictCheckAt 10 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 119) 10 119:=by decide +kernel
  have hfast:StrictAtFast (row 10 119) 10 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 119) 10 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 119) 10 119 hvalid hfast

theorem sr10p120:∀ i ∈ List.range 1,StrictCheckAt 10 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 120) 10 120:=by decide +kernel
  have hfast:StrictAtFast (row 10 120) 10 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 120) 10 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 120) 10 120 hvalid hfast

theorem sr10p121:∀ i ∈ List.range 1,StrictCheckAt 10 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 121) 10 121:=by decide +kernel
  have hfast:StrictAtFast (row 10 121) 10 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 121) 10 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 121) 10 121 hvalid hfast

theorem sr10p122:∀ i ∈ List.range 1,StrictCheckAt 10 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 122) 10 122:=by decide +kernel
  have hfast:StrictAtFast (row 10 122) 10 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 122) 10 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 122) 10 122 hvalid hfast

theorem sr10p123:∀ i ∈ List.range 1,StrictCheckAt 10 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 123) 10 123:=by decide +kernel
  have hfast:StrictAtFast (row 10 123) 10 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 123) 10 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 123) 10 123 hvalid hfast

theorem sr10p124:∀ i ∈ List.range 1,StrictCheckAt 10 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 124) 10 124:=by decide +kernel
  have hfast:StrictAtFast (row 10 124) 10 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 124) 10 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 124) 10 124 hvalid hfast

theorem sr10p125:∀ i ∈ List.range 1,StrictCheckAt 10 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 125) 10 125:=by decide +kernel
  have hfast:StrictAtFast (row 10 125) 10 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 125) 10 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 125) 10 125 hvalid hfast

theorem sr10p126:∀ i ∈ List.range 1,StrictCheckAt 10 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 126) 10 126:=by decide +kernel
  have hfast:StrictAtFast (row 10 126) 10 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 126) 10 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 126) 10 126 hvalid hfast

theorem sr10p127:∀ i ∈ List.range 1,StrictCheckAt 10 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 127) 10 127:=by decide +kernel
  have hfast:StrictAtFast (row 10 127) 10 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 127) 10 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 127) 10 127 hvalid hfast

theorem sr10p128:∀ i ∈ List.range 1,StrictCheckAt 10 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 128) 10 128:=by decide +kernel
  have hfast:StrictAtFast (row 10 128) 10 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 128) 10 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 128) 10 128 hvalid hfast

theorem sr10p129:∀ i ∈ List.range 1,StrictCheckAt 10 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 129) 10 129:=by decide +kernel
  have hfast:StrictAtFast (row 10 129) 10 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 129) 10 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 129) 10 129 hvalid hfast

theorem sr10p130:∀ i ∈ List.range 1,StrictCheckAt 10 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 130) 10 130:=by decide +kernel
  have hfast:StrictAtFast (row 10 130) 10 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 130) 10 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 130) 10 130 hvalid hfast

theorem sr10p131:∀ i ∈ List.range 1,StrictCheckAt 10 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 131 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 131) 10 131:=by decide +kernel
  have hfast:StrictAtFast (row 10 131) 10 131:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 131) 10 131 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 131) 10 131 hvalid hfast

theorem sr10p132:∀ i ∈ List.range 1,StrictCheckAt 10 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 10 132 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 10 132) 10 132:=by decide +kernel
  have hfast:StrictAtFast (row 10 132) 10 132:=
    BoundaryTailStrictConvex.endpoints_sound (row 10 132) 10 132 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 10 132) 10 132 hvalid hfast

theorem br10p0:∀ i ∈ List.range 4,BaseCheckAt 10 (0+i):=by decide +kernel

theorem br10p1:∀ i ∈ List.range 4,BaseCheckAt 10 (4+i):=by decide +kernel

theorem br10p2:∀ i ∈ List.range 4,BaseCheckAt 10 (8+i):=by decide +kernel

theorem br10p3:∀ i ∈ List.range 4,BaseCheckAt 10 (12+i):=by decide +kernel

theorem br10p4:∀ i ∈ List.range 4,BaseCheckAt 10 (16+i):=by decide +kernel

theorem br10p5:∀ i ∈ List.range 4,BaseCheckAt 10 (20+i):=by decide +kernel

theorem br10p6:∀ i ∈ List.range 4,BaseCheckAt 10 (24+i):=by decide +kernel

theorem br10p7:∀ i ∈ List.range 4,BaseCheckAt 10 (28+i):=by decide +kernel

theorem br10p8:∀ i ∈ List.range 4,BaseCheckAt 10 (32+i):=by decide +kernel

theorem br10p9:∀ i ∈ List.range 4,BaseCheckAt 10 (36+i):=by decide +kernel

theorem br10p10:∀ i ∈ List.range 4,BaseCheckAt 10 (40+i):=by decide +kernel

theorem br10p11:∀ i ∈ List.range 4,BaseCheckAt 10 (44+i):=by decide +kernel

theorem br10p12:∀ i ∈ List.range 4,BaseCheckAt 10 (48+i):=by decide +kernel

theorem br10p13:∀ i ∈ List.range 4,BaseCheckAt 10 (52+i):=by decide +kernel

theorem br10p14:∀ i ∈ List.range 4,BaseCheckAt 10 (56+i):=by decide +kernel

theorem br10p15:∀ i ∈ List.range 4,BaseCheckAt 10 (60+i):=by decide +kernel



theorem br10p16:∀ i ∈ List.range 4,BaseCheckAt 10 (64+i):=by decide +kernel

theorem br10p17:∀ i ∈ List.range 4,BaseCheckAt 10 (68+i):=by decide +kernel

theorem br10p18:∀ i ∈ List.range 4,BaseCheckAt 10 (72+i):=by decide +kernel

theorem br10p19:∀ i ∈ List.range 4,BaseCheckAt 10 (76+i):=by decide +kernel

theorem br10p20:∀ i ∈ List.range 4,BaseCheckAt 10 (80+i):=by decide +kernel

theorem br10p21:∀ i ∈ List.range 4,BaseCheckAt 10 (84+i):=by decide +kernel

theorem br10p22:∀ i ∈ List.range 4,BaseCheckAt 10 (88+i):=by decide +kernel

theorem br10p23:∀ i ∈ List.range 4,BaseCheckAt 10 (92+i):=by decide +kernel

theorem br10p24:∀ i ∈ List.range 4,BaseCheckAt 10 (96+i):=by decide +kernel

theorem br10p25:∀ i ∈ List.range 4,BaseCheckAt 10 (100+i):=by decide +kernel

theorem br10p26:∀ i ∈ List.range 4,BaseCheckAt 10 (104+i):=by decide +kernel

theorem br10p27:∀ i ∈ List.range 4,BaseCheckAt 10 (108+i):=by decide +kernel

theorem br10p28:∀ i ∈ List.range 4,BaseCheckAt 10 (112+i):=by decide +kernel

theorem br10p29:∀ i ∈ List.range 4,BaseCheckAt 10 (116+i):=by decide +kernel

theorem br10p30:∀ i ∈ List.range 4,BaseCheckAt 10 (120+i):=by decide +kernel

theorem br10p31:∀ i ∈ List.range 4,BaseCheckAt 10 (124+i):=by decide +kernel



theorem br10p32:∀ i ∈ List.range 4,BaseCheckAt 10 (128+i):=by decide +kernel

theorem br10p33:∀ i ∈ List.range 1,BaseCheckAt 10 (132+i):=by decide +kernel



theorem cr10:∀ V ∈ List.range 133,CorrectAt 10 V:=by
  intro V hV
  have hv:V < 133:=List.mem_range.mp hV
  by_cases h0_17:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr10p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr10p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr10p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr10p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr10p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr10p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr10p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr10p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_17:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr10p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr10p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr10p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr10p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_17:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr10p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr10p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_17:V < 120
        · have h:=cr10p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h15_17:V < 128
          · have h:=cr10p15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=cr10p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem zr10:∀ V ∈ List.range 133,ZeroCheckAt 10 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 10 V (by omega) (by omega) (by omega)
theorem sr10:∀ V ∈ List.range 133,StrictCheckAt 10 V:=by
  intro V hV
  have hv:V < 133:=List.mem_range.mp hV
  by_cases h0_133:V < 66
  · by_cases h0_66:V < 33
    · by_cases h0_33:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have h:=sr10p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
              · have h:=sr10p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
            · by_cases h2_4:V < 3
              · have h:=sr10p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
              · have h:=sr10p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have h:=sr10p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
              · have h:=sr10p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
            · by_cases h6_8:V < 7
              · have h:=sr10p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
              · have h:=sr10p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have h:=sr10p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr10p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
            · by_cases h10_12:V < 11
              · have h:=sr10p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr10p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have h:=sr10p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr10p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
            · by_cases h14_16:V < 15
              · have h:=sr10p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
              · have h:=sr10p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
      · by_cases h16_33:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have h:=sr10p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr10p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
            · by_cases h18_20:V < 19
              · have h:=sr10p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr10p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have h:=sr10p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr10p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr10p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr10p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
        · by_cases h24_33:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr10p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr10p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr10p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr10p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
          · by_cases h28_33:V < 30
            · by_cases h28_30:V < 29
              · have h:=sr10p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr10p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_33:V < 31
              · have h:=sr10p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · by_cases h31_33:V < 32
                · have h:=sr10p31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
                · have h:=sr10p32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
    · by_cases h33_66:V < 49
      · by_cases h33_49:V < 41
        · by_cases h33_41:V < 37
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have h:=sr10p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr10p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
            · by_cases h35_37:V < 36
              · have h:=sr10p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr10p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have h:=sr10p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr10p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
            · by_cases h39_41:V < 40
              · have h:=sr10p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr10p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · by_cases h41_49:V < 45
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have h:=sr10p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr10p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr10p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr10p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr10p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr10p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr10p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr10p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
      · by_cases h49_66:V < 57
        · by_cases h49_57:V < 53
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have h:=sr10p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr10p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
            · by_cases h51_53:V < 52
              · have h:=sr10p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr10p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have h:=sr10p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr10p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
            · by_cases h55_57:V < 56
              · have h:=sr10p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr10p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · by_cases h57_66:V < 61
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have h:=sr10p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr10p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
            · by_cases h59_61:V < 60
              · have h:=sr10p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr10p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · by_cases h61_66:V < 63
            · by_cases h61_63:V < 62
              · have h:=sr10p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr10p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
            · by_cases h63_66:V < 64
              · have h:=sr10p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · by_cases h64_66:V < 65
                · have h:=sr10p64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
                · have h:=sr10p65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
  · by_cases h66_133:V < 99
    · by_cases h66_99:V < 82
      · by_cases h66_82:V < 74
        · by_cases h66_74:V < 70
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have h:=sr10p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr10p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
            · by_cases h68_70:V < 69
              · have h:=sr10p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr10p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have h:=sr10p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr10p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
            · by_cases h72_74:V < 73
              · have h:=sr10p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr10p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
        · by_cases h74_82:V < 78
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have h:=sr10p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr10p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
            · by_cases h76_78:V < 77
              · have h:=sr10p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr10p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have h:=sr10p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr10p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
            · by_cases h80_82:V < 81
              · have h:=sr10p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr10p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
      · by_cases h82_99:V < 90
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have h:=sr10p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr10p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
            · by_cases h84_86:V < 85
              · have h:=sr10p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr10p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have h:=sr10p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr10p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
            · by_cases h88_90:V < 89
              · have h:=sr10p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr10p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
        · by_cases h90_99:V < 94
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have h:=sr10p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr10p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr10p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr10p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
          · by_cases h94_99:V < 96
            · by_cases h94_96:V < 95
              · have h:=sr10p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr10p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
            · by_cases h96_99:V < 97
              · have h:=sr10p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · by_cases h97_99:V < 98
                · have h:=sr10p97 (V-97) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
                · have h:=sr10p98 (V-98) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
    · by_cases h99_133:V < 116
      · by_cases h99_116:V < 107
        · by_cases h99_107:V < 103
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have h:=sr10p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr10p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
            · by_cases h101_103:V < 102
              · have h:=sr10p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr10p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have h:=sr10p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr10p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
            · by_cases h105_107:V < 106
              · have h:=sr10p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr10p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
        · by_cases h107_116:V < 111
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have h:=sr10p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr10p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
            · by_cases h109_111:V < 110
              · have h:=sr10p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr10p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
          · by_cases h111_116:V < 113
            · by_cases h111_113:V < 112
              · have h:=sr10p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr10p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
            · by_cases h113_116:V < 114
              · have h:=sr10p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · by_cases h114_116:V < 115
                · have h:=sr10p114 (V-114) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
                · have h:=sr10p115 (V-115) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
      · by_cases h116_133:V < 124
        · by_cases h116_124:V < 120
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have h:=sr10p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr10p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
            · by_cases h118_120:V < 119
              · have h:=sr10p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr10p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have h:=sr10p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
              · have h:=sr10p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
            · by_cases h122_124:V < 123
              · have h:=sr10p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
              · have h:=sr10p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
        · by_cases h124_133:V < 128
          · by_cases h124_128:V < 126
            · by_cases h124_126:V < 125
              · have h:=sr10p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
              · have h:=sr10p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
            · by_cases h126_128:V < 127
              · have h:=sr10p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h
              · have h:=sr10p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using h
          · by_cases h128_133:V < 130
            · by_cases h128_130:V < 129
              · have h:=sr10p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
              · have h:=sr10p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using h
            · by_cases h130_133:V < 131
              · have h:=sr10p130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using h
              · by_cases h131_133:V < 132
                · have h:=sr10p131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using h
                · have h:=sr10p132 (V-132) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using h

theorem br10:∀ V ∈ List.range 133,BaseCheckAt 10 V:=by
  intro V hV
  have hv:V < 133:=List.mem_range.mp hV
  by_cases h0_34:V < 68
  · by_cases h0_17:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br10p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br10p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br10p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br10p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br10p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br10p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br10p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br10p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_17:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br10p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br10p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br10p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br10p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_17:V < 56
        · by_cases h12_14:V < 52
          · have h:=br10p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br10p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_17:V < 60
          · have h:=br10p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · by_cases h15_17:V < 64
            · have h:=br10p15 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · have h:=br10p16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
  · by_cases h17_34:V < 100
    · by_cases h17_25:V < 84
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br10p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br10p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br10p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br10p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
      · by_cases h21_25:V < 92
        · by_cases h21_23:V < 88
          · have h:=br10p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br10p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h23_25:V < 96
          · have h:=br10p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br10p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
    · by_cases h25_34:V < 116
      · by_cases h25_29:V < 108
        · by_cases h25_27:V < 104
          · have h:=br10p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br10p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h27_29:V < 112
          · have h:=br10p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br10p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
      · by_cases h29_34:V < 124
        · by_cases h29_31:V < 120
          · have h:=br10p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · have h:=br10p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
        · by_cases h31_34:V < 128
          · have h:=br10p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
          · by_cases h32_34:V < 132
            · have h:=br10p32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
            · have h:=br10p33 (V-132) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
