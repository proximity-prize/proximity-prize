import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr14p0:∀ i ∈ List.range 8,CorrectAt 14 (0+i):=by decide +kernel

theorem cr14p1:∀ i ∈ List.range 8,CorrectAt 14 (8+i):=by decide +kernel

theorem cr14p2:∀ i ∈ List.range 8,CorrectAt 14 (16+i):=by decide +kernel

theorem cr14p3:∀ i ∈ List.range 8,CorrectAt 14 (24+i):=by decide +kernel

theorem cr14p4:∀ i ∈ List.range 8,CorrectAt 14 (32+i):=by decide +kernel

theorem cr14p5:∀ i ∈ List.range 8,CorrectAt 14 (40+i):=by decide +kernel

theorem cr14p6:∀ i ∈ List.range 8,CorrectAt 14 (48+i):=by decide +kernel

theorem cr14p7:∀ i ∈ List.range 8,CorrectAt 14 (56+i):=by decide +kernel

theorem cr14p8:∀ i ∈ List.range 8,CorrectAt 14 (64+i):=by decide +kernel

theorem cr14p9:∀ i ∈ List.range 8,CorrectAt 14 (72+i):=by decide +kernel

theorem cr14p10:∀ i ∈ List.range 8,CorrectAt 14 (80+i):=by decide +kernel

theorem cr14p11:∀ i ∈ List.range 8,CorrectAt 14 (88+i):=by decide +kernel

theorem cr14p12:∀ i ∈ List.range 8,CorrectAt 14 (96+i):=by decide +kernel

theorem cr14p13:∀ i ∈ List.range 8,CorrectAt 14 (104+i):=by decide +kernel

theorem cr14p14:∀ i ∈ List.range 8,CorrectAt 14 (112+i):=by decide +kernel

theorem cr14p15:∀ i ∈ List.range 8,CorrectAt 14 (120+i):=by decide +kernel

theorem cr14p16:∀ i ∈ List.range 1,CorrectAt 14 (128+i):=by decide +kernel

theorem sr14p0:∀ i ∈ List.range 1,StrictCheckAt 14 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 0) 14 0:=by decide +kernel
  have hfast:StrictAtFast (row 14 0) 14 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 0) 14 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 0) 14 0 hvalid hfast

theorem sr14p1:∀ i ∈ List.range 1,StrictCheckAt 14 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 1) 14 1:=by decide +kernel
  have hfast:StrictAtFast (row 14 1) 14 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 1) 14 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 1) 14 1 hvalid hfast

theorem sr14p2:∀ i ∈ List.range 1,StrictCheckAt 14 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 2) 14 2:=by decide +kernel
  have hfast:StrictAtFast (row 14 2) 14 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 2) 14 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 2) 14 2 hvalid hfast

theorem sr14p3:∀ i ∈ List.range 1,StrictCheckAt 14 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 3) 14 3:=by decide +kernel
  have hfast:StrictAtFast (row 14 3) 14 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 3) 14 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 3) 14 3 hvalid hfast

theorem sr14p4:∀ i ∈ List.range 1,StrictCheckAt 14 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 4) 14 4:=by decide +kernel
  have hfast:StrictAtFast (row 14 4) 14 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 4) 14 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 4) 14 4 hvalid hfast

theorem sr14p5:∀ i ∈ List.range 1,StrictCheckAt 14 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 5) 14 5:=by decide +kernel
  have hfast:StrictAtFast (row 14 5) 14 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 5) 14 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 5) 14 5 hvalid hfast

theorem sr14p6:∀ i ∈ List.range 1,StrictCheckAt 14 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 6) 14 6:=by decide +kernel
  have hfast:StrictAtFast (row 14 6) 14 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 6) 14 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 6) 14 6 hvalid hfast

theorem sr14p7:∀ i ∈ List.range 1,StrictCheckAt 14 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 7) 14 7:=by decide +kernel
  have hfast:StrictAtFast (row 14 7) 14 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 7) 14 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 7) 14 7 hvalid hfast

theorem sr14p8:∀ i ∈ List.range 1,StrictCheckAt 14 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 8) 14 8:=by decide +kernel
  have hfast:StrictAtFast (row 14 8) 14 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 8) 14 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 8) 14 8 hvalid hfast

theorem sr14p9:∀ i ∈ List.range 1,StrictCheckAt 14 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 9) 14 9:=by decide +kernel
  have hfast:StrictAtFast (row 14 9) 14 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 9) 14 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 9) 14 9 hvalid hfast

theorem sr14p10:∀ i ∈ List.range 1,StrictCheckAt 14 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 10) 14 10:=by decide +kernel
  have hfast:StrictAtFast (row 14 10) 14 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 10) 14 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 10) 14 10 hvalid hfast

theorem sr14p11:∀ i ∈ List.range 1,StrictCheckAt 14 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 11) 14 11:=by decide +kernel
  have hfast:StrictAtFast (row 14 11) 14 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 11) 14 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 11) 14 11 hvalid hfast

theorem sr14p12:∀ i ∈ List.range 1,StrictCheckAt 14 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 12) 14 12:=by decide +kernel
  have hfast:StrictAtFast (row 14 12) 14 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 12) 14 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 12) 14 12 hvalid hfast

theorem sr14p13:∀ i ∈ List.range 1,StrictCheckAt 14 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 13) 14 13:=by decide +kernel
  have hfast:StrictAtFast (row 14 13) 14 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 13) 14 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 13) 14 13 hvalid hfast

theorem sr14p14:∀ i ∈ List.range 1,StrictCheckAt 14 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 14) 14 14:=by decide +kernel
  have hfast:StrictAtFast (row 14 14) 14 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 14) 14 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 14) 14 14 hvalid hfast

theorem sr14p15:∀ i ∈ List.range 1,StrictCheckAt 14 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 15) 14 15:=by decide +kernel
  have hfast:StrictAtFast (row 14 15) 14 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 15) 14 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 15) 14 15 hvalid hfast

theorem sr14p16:∀ i ∈ List.range 1,StrictCheckAt 14 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 16) 14 16:=by decide +kernel
  have hfast:StrictAtFast (row 14 16) 14 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 16) 14 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 16) 14 16 hvalid hfast

theorem sr14p17:∀ i ∈ List.range 1,StrictCheckAt 14 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 17) 14 17:=by decide +kernel
  have hfast:StrictAtFast (row 14 17) 14 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 17) 14 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 17) 14 17 hvalid hfast

theorem sr14p18:∀ i ∈ List.range 1,StrictCheckAt 14 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 18) 14 18:=by decide +kernel
  have hfast:StrictAtFast (row 14 18) 14 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 18) 14 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 18) 14 18 hvalid hfast

theorem sr14p19:∀ i ∈ List.range 1,StrictCheckAt 14 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 19) 14 19:=by decide +kernel
  have hfast:StrictAtFast (row 14 19) 14 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 19) 14 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 19) 14 19 hvalid hfast

theorem sr14p20:∀ i ∈ List.range 1,StrictCheckAt 14 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 20) 14 20:=by decide +kernel
  have hfast:StrictAtFast (row 14 20) 14 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 20) 14 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 20) 14 20 hvalid hfast

theorem sr14p21:∀ i ∈ List.range 1,StrictCheckAt 14 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 21) 14 21:=by decide +kernel
  have hfast:StrictAtFast (row 14 21) 14 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 21) 14 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 21) 14 21 hvalid hfast

theorem sr14p22:∀ i ∈ List.range 1,StrictCheckAt 14 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 22) 14 22:=by decide +kernel
  have hfast:StrictAtFast (row 14 22) 14 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 22) 14 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 22) 14 22 hvalid hfast

theorem sr14p23:∀ i ∈ List.range 1,StrictCheckAt 14 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 23) 14 23:=by decide +kernel
  have hfast:StrictAtFast (row 14 23) 14 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 23) 14 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 23) 14 23 hvalid hfast

theorem sr14p24:∀ i ∈ List.range 1,StrictCheckAt 14 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 24) 14 24:=by decide +kernel
  have hfast:StrictAtFast (row 14 24) 14 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 24) 14 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 24) 14 24 hvalid hfast

theorem sr14p25:∀ i ∈ List.range 1,StrictCheckAt 14 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 25) 14 25:=by decide +kernel
  have hfast:StrictAtFast (row 14 25) 14 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 25) 14 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 25) 14 25 hvalid hfast

theorem sr14p26:∀ i ∈ List.range 1,StrictCheckAt 14 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 26) 14 26:=by decide +kernel
  have hfast:StrictAtFast (row 14 26) 14 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 26) 14 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 26) 14 26 hvalid hfast

theorem sr14p27:∀ i ∈ List.range 1,StrictCheckAt 14 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 27) 14 27:=by decide +kernel
  have hfast:StrictAtFast (row 14 27) 14 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 27) 14 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 27) 14 27 hvalid hfast

theorem sr14p28:∀ i ∈ List.range 1,StrictCheckAt 14 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 28) 14 28:=by decide +kernel
  have hfast:StrictAtFast (row 14 28) 14 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 28) 14 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 28) 14 28 hvalid hfast

theorem sr14p29:∀ i ∈ List.range 1,StrictCheckAt 14 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 29) 14 29:=by decide +kernel
  have hfast:StrictAtFast (row 14 29) 14 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 29) 14 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 29) 14 29 hvalid hfast

theorem sr14p30:∀ i ∈ List.range 1,StrictCheckAt 14 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 30) 14 30:=by decide +kernel
  have hfast:StrictAtFast (row 14 30) 14 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 30) 14 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 30) 14 30 hvalid hfast

theorem sr14p31:∀ i ∈ List.range 1,StrictCheckAt 14 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 31) 14 31:=by decide +kernel
  have hfast:StrictAtFast (row 14 31) 14 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 31) 14 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 31) 14 31 hvalid hfast

theorem sr14p32:∀ i ∈ List.range 1,StrictCheckAt 14 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 32) 14 32:=by decide +kernel
  have hfast:StrictAtFast (row 14 32) 14 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 32) 14 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 32) 14 32 hvalid hfast

theorem sr14p33:∀ i ∈ List.range 1,StrictCheckAt 14 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 33) 14 33:=by decide +kernel
  have hfast:StrictAtFast (row 14 33) 14 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 33) 14 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 33) 14 33 hvalid hfast

theorem sr14p34:∀ i ∈ List.range 1,StrictCheckAt 14 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 34) 14 34:=by decide +kernel
  have hfast:StrictAtFast (row 14 34) 14 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 34) 14 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 34) 14 34 hvalid hfast

theorem sr14p35:∀ i ∈ List.range 1,StrictCheckAt 14 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 35) 14 35:=by decide +kernel
  have hfast:StrictAtFast (row 14 35) 14 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 35) 14 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 35) 14 35 hvalid hfast

theorem sr14p36:∀ i ∈ List.range 1,StrictCheckAt 14 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 36) 14 36:=by decide +kernel
  have hfast:StrictAtFast (row 14 36) 14 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 36) 14 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 36) 14 36 hvalid hfast

theorem sr14p37:∀ i ∈ List.range 1,StrictCheckAt 14 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 37) 14 37:=by decide +kernel
  have hfast:StrictAtFast (row 14 37) 14 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 37) 14 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 37) 14 37 hvalid hfast

theorem sr14p38:∀ i ∈ List.range 1,StrictCheckAt 14 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 38) 14 38:=by decide +kernel
  have hfast:StrictAtFast (row 14 38) 14 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 38) 14 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 38) 14 38 hvalid hfast

theorem sr14p39:∀ i ∈ List.range 1,StrictCheckAt 14 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 39) 14 39:=by decide +kernel
  have hfast:StrictAtFast (row 14 39) 14 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 39) 14 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 39) 14 39 hvalid hfast

theorem sr14p40:∀ i ∈ List.range 1,StrictCheckAt 14 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 40) 14 40:=by decide +kernel
  have hfast:StrictAtFast (row 14 40) 14 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 40) 14 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 40) 14 40 hvalid hfast

theorem sr14p41:∀ i ∈ List.range 1,StrictCheckAt 14 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 41) 14 41:=by decide +kernel
  have hfast:StrictAtFast (row 14 41) 14 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 41) 14 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 41) 14 41 hvalid hfast

theorem sr14p42:∀ i ∈ List.range 1,StrictCheckAt 14 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 42) 14 42:=by decide +kernel
  have hfast:StrictAtFast (row 14 42) 14 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 42) 14 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 42) 14 42 hvalid hfast

theorem sr14p43:∀ i ∈ List.range 1,StrictCheckAt 14 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 43) 14 43:=by decide +kernel
  have hfast:StrictAtFast (row 14 43) 14 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 43) 14 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 43) 14 43 hvalid hfast

theorem sr14p44:∀ i ∈ List.range 1,StrictCheckAt 14 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 44) 14 44:=by decide +kernel
  have hfast:StrictAtFast (row 14 44) 14 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 44) 14 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 44) 14 44 hvalid hfast

theorem sr14p45:∀ i ∈ List.range 1,StrictCheckAt 14 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 45) 14 45:=by decide +kernel
  have hfast:StrictAtFast (row 14 45) 14 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 45) 14 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 45) 14 45 hvalid hfast

theorem sr14p46:∀ i ∈ List.range 1,StrictCheckAt 14 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 46) 14 46:=by decide +kernel
  have hfast:StrictAtFast (row 14 46) 14 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 46) 14 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 46) 14 46 hvalid hfast

theorem sr14p47:∀ i ∈ List.range 1,StrictCheckAt 14 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 47) 14 47:=by decide +kernel
  have hfast:StrictAtFast (row 14 47) 14 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 47) 14 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 47) 14 47 hvalid hfast

theorem sr14p48:∀ i ∈ List.range 1,StrictCheckAt 14 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 48) 14 48:=by decide +kernel
  have hfast:StrictAtFast (row 14 48) 14 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 48) 14 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 48) 14 48 hvalid hfast

theorem sr14p49:∀ i ∈ List.range 1,StrictCheckAt 14 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 49) 14 49:=by decide +kernel
  have hfast:StrictAtFast (row 14 49) 14 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 49) 14 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 49) 14 49 hvalid hfast

theorem sr14p50:∀ i ∈ List.range 1,StrictCheckAt 14 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 50) 14 50:=by decide +kernel
  have hfast:StrictAtFast (row 14 50) 14 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 50) 14 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 50) 14 50 hvalid hfast

theorem sr14p51:∀ i ∈ List.range 1,StrictCheckAt 14 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 51) 14 51:=by decide +kernel
  have hfast:StrictAtFast (row 14 51) 14 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 51) 14 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 51) 14 51 hvalid hfast

theorem sr14p52:∀ i ∈ List.range 1,StrictCheckAt 14 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 52) 14 52:=by decide +kernel
  have hfast:StrictAtFast (row 14 52) 14 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 52) 14 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 52) 14 52 hvalid hfast

theorem sr14p53:∀ i ∈ List.range 1,StrictCheckAt 14 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 53) 14 53:=by decide +kernel
  have hfast:StrictAtFast (row 14 53) 14 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 53) 14 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 53) 14 53 hvalid hfast

theorem sr14p54:∀ i ∈ List.range 1,StrictCheckAt 14 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 54) 14 54:=by decide +kernel
  have hfast:StrictAtFast (row 14 54) 14 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 54) 14 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 54) 14 54 hvalid hfast

theorem sr14p55:∀ i ∈ List.range 1,StrictCheckAt 14 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 55) 14 55:=by decide +kernel
  have hfast:StrictAtFast (row 14 55) 14 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 55) 14 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 55) 14 55 hvalid hfast

theorem sr14p56:∀ i ∈ List.range 1,StrictCheckAt 14 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 56) 14 56:=by decide +kernel
  have hfast:StrictAtFast (row 14 56) 14 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 56) 14 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 56) 14 56 hvalid hfast

theorem sr14p57:∀ i ∈ List.range 1,StrictCheckAt 14 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 57) 14 57:=by decide +kernel
  have hfast:StrictAtFast (row 14 57) 14 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 57) 14 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 57) 14 57 hvalid hfast

theorem sr14p58:∀ i ∈ List.range 1,StrictCheckAt 14 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 58) 14 58:=by decide +kernel
  have hfast:StrictAtFast (row 14 58) 14 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 58) 14 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 58) 14 58 hvalid hfast

theorem sr14p59:∀ i ∈ List.range 1,StrictCheckAt 14 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 59) 14 59:=by decide +kernel
  have hfast:StrictAtFast (row 14 59) 14 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 59) 14 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 59) 14 59 hvalid hfast

theorem sr14p60:∀ i ∈ List.range 1,StrictCheckAt 14 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 60) 14 60:=by decide +kernel
  have hfast:StrictAtFast (row 14 60) 14 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 60) 14 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 60) 14 60 hvalid hfast

theorem sr14p61:∀ i ∈ List.range 1,StrictCheckAt 14 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 61) 14 61:=by decide +kernel
  have hfast:StrictAtFast (row 14 61) 14 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 61) 14 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 61) 14 61 hvalid hfast

theorem sr14p62:∀ i ∈ List.range 1,StrictCheckAt 14 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 62) 14 62:=by decide +kernel
  have hfast:StrictAtFast (row 14 62) 14 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 62) 14 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 62) 14 62 hvalid hfast

theorem sr14p63:∀ i ∈ List.range 1,StrictCheckAt 14 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 63) 14 63:=by decide +kernel
  have hfast:StrictAtFast (row 14 63) 14 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 63) 14 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 63) 14 63 hvalid hfast

theorem sr14p64:∀ i ∈ List.range 1,StrictCheckAt 14 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 64) 14 64:=by decide +kernel
  have hfast:StrictAtFast (row 14 64) 14 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 64) 14 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 64) 14 64 hvalid hfast

theorem sr14p65:∀ i ∈ List.range 1,StrictCheckAt 14 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 65) 14 65:=by decide +kernel
  have hfast:StrictAtFast (row 14 65) 14 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 65) 14 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 65) 14 65 hvalid hfast

theorem sr14p66:∀ i ∈ List.range 1,StrictCheckAt 14 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 66) 14 66:=by decide +kernel
  have hfast:StrictAtFast (row 14 66) 14 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 66) 14 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 66) 14 66 hvalid hfast

theorem sr14p67:∀ i ∈ List.range 1,StrictCheckAt 14 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 67) 14 67:=by decide +kernel
  have hfast:StrictAtFast (row 14 67) 14 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 67) 14 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 67) 14 67 hvalid hfast

theorem sr14p68:∀ i ∈ List.range 1,StrictCheckAt 14 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 68) 14 68:=by decide +kernel
  have hfast:StrictAtFast (row 14 68) 14 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 68) 14 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 68) 14 68 hvalid hfast

theorem sr14p69:∀ i ∈ List.range 1,StrictCheckAt 14 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 69) 14 69:=by decide +kernel
  have hfast:StrictAtFast (row 14 69) 14 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 69) 14 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 69) 14 69 hvalid hfast

theorem sr14p70:∀ i ∈ List.range 1,StrictCheckAt 14 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 70) 14 70:=by decide +kernel
  have hfast:StrictAtFast (row 14 70) 14 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 70) 14 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 70) 14 70 hvalid hfast

theorem sr14p71:∀ i ∈ List.range 1,StrictCheckAt 14 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 71) 14 71:=by decide +kernel
  have hfast:StrictAtFast (row 14 71) 14 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 71) 14 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 71) 14 71 hvalid hfast

theorem sr14p72:∀ i ∈ List.range 1,StrictCheckAt 14 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 72) 14 72:=by decide +kernel
  have hfast:StrictAtFast (row 14 72) 14 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 72) 14 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 72) 14 72 hvalid hfast

theorem sr14p73:∀ i ∈ List.range 1,StrictCheckAt 14 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 73) 14 73:=by decide +kernel
  have hfast:StrictAtFast (row 14 73) 14 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 73) 14 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 73) 14 73 hvalid hfast

theorem sr14p74:∀ i ∈ List.range 1,StrictCheckAt 14 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 74) 14 74:=by decide +kernel
  have hfast:StrictAtFast (row 14 74) 14 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 74) 14 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 74) 14 74 hvalid hfast

theorem sr14p75:∀ i ∈ List.range 1,StrictCheckAt 14 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 75) 14 75:=by decide +kernel
  have hfast:StrictAtFast (row 14 75) 14 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 75) 14 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 75) 14 75 hvalid hfast

theorem sr14p76:∀ i ∈ List.range 1,StrictCheckAt 14 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 76) 14 76:=by decide +kernel
  have hfast:StrictAtFast (row 14 76) 14 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 76) 14 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 76) 14 76 hvalid hfast

theorem sr14p77:∀ i ∈ List.range 1,StrictCheckAt 14 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 77) 14 77:=by decide +kernel
  have hfast:StrictAtFast (row 14 77) 14 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 77) 14 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 77) 14 77 hvalid hfast

theorem sr14p78:∀ i ∈ List.range 1,StrictCheckAt 14 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 78) 14 78:=by decide +kernel
  have hfast:StrictAtFast (row 14 78) 14 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 78) 14 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 78) 14 78 hvalid hfast

theorem sr14p79:∀ i ∈ List.range 1,StrictCheckAt 14 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 79) 14 79:=by decide +kernel
  have hfast:StrictAtFast (row 14 79) 14 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 79) 14 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 79) 14 79 hvalid hfast

theorem sr14p80:∀ i ∈ List.range 1,StrictCheckAt 14 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 80) 14 80:=by decide +kernel
  have hfast:StrictAtFast (row 14 80) 14 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 80) 14 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 80) 14 80 hvalid hfast

theorem sr14p81:∀ i ∈ List.range 1,StrictCheckAt 14 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 81) 14 81:=by decide +kernel
  have hfast:StrictAtFast (row 14 81) 14 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 81) 14 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 81) 14 81 hvalid hfast

theorem sr14p82:∀ i ∈ List.range 1,StrictCheckAt 14 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 82) 14 82:=by decide +kernel
  have hfast:StrictAtFast (row 14 82) 14 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 82) 14 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 82) 14 82 hvalid hfast

theorem sr14p83:∀ i ∈ List.range 1,StrictCheckAt 14 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 83) 14 83:=by decide +kernel
  have hfast:StrictAtFast (row 14 83) 14 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 83) 14 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 83) 14 83 hvalid hfast

theorem sr14p84:∀ i ∈ List.range 1,StrictCheckAt 14 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 84) 14 84:=by decide +kernel
  have hfast:StrictAtFast (row 14 84) 14 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 84) 14 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 84) 14 84 hvalid hfast

theorem sr14p85:∀ i ∈ List.range 1,StrictCheckAt 14 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 85) 14 85:=by decide +kernel
  have hfast:StrictAtFast (row 14 85) 14 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 85) 14 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 85) 14 85 hvalid hfast

theorem sr14p86:∀ i ∈ List.range 1,StrictCheckAt 14 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 86) 14 86:=by decide +kernel
  have hfast:StrictAtFast (row 14 86) 14 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 86) 14 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 86) 14 86 hvalid hfast

theorem sr14p87:∀ i ∈ List.range 1,StrictCheckAt 14 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 87) 14 87:=by decide +kernel
  have hfast:StrictAtFast (row 14 87) 14 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 87) 14 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 87) 14 87 hvalid hfast

theorem sr14p88:∀ i ∈ List.range 1,StrictCheckAt 14 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 88) 14 88:=by decide +kernel
  have hfast:StrictAtFast (row 14 88) 14 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 88) 14 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 88) 14 88 hvalid hfast

theorem sr14p89:∀ i ∈ List.range 1,StrictCheckAt 14 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 89) 14 89:=by decide +kernel
  have hfast:StrictAtFast (row 14 89) 14 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 89) 14 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 89) 14 89 hvalid hfast

theorem sr14p90:∀ i ∈ List.range 1,StrictCheckAt 14 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 90) 14 90:=by decide +kernel
  have hfast:StrictAtFast (row 14 90) 14 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 90) 14 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 90) 14 90 hvalid hfast

theorem sr14p91:∀ i ∈ List.range 1,StrictCheckAt 14 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 91) 14 91:=by decide +kernel
  have hfast:StrictAtFast (row 14 91) 14 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 91) 14 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 91) 14 91 hvalid hfast

theorem sr14p92:∀ i ∈ List.range 1,StrictCheckAt 14 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 92) 14 92:=by decide +kernel
  have hfast:StrictAtFast (row 14 92) 14 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 92) 14 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 92) 14 92 hvalid hfast

theorem sr14p93:∀ i ∈ List.range 1,StrictCheckAt 14 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 93) 14 93:=by decide +kernel
  have hfast:StrictAtFast (row 14 93) 14 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 93) 14 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 93) 14 93 hvalid hfast

theorem sr14p94:∀ i ∈ List.range 1,StrictCheckAt 14 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 94) 14 94:=by decide +kernel
  have hfast:StrictAtFast (row 14 94) 14 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 94) 14 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 94) 14 94 hvalid hfast

theorem sr14p95:∀ i ∈ List.range 1,StrictCheckAt 14 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 95) 14 95:=by decide +kernel
  have hfast:StrictAtFast (row 14 95) 14 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 95) 14 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 95) 14 95 hvalid hfast

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

theorem sr14p112:∀ i ∈ List.range 1,StrictCheckAt 14 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 112) 14 112:=by decide +kernel
  have hfast:StrictAtFast (row 14 112) 14 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 112) 14 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 112) 14 112 hvalid hfast

theorem sr14p113:∀ i ∈ List.range 1,StrictCheckAt 14 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 113) 14 113:=by decide +kernel
  have hfast:StrictAtFast (row 14 113) 14 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 113) 14 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 113) 14 113 hvalid hfast

theorem sr14p114:∀ i ∈ List.range 1,StrictCheckAt 14 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 114) 14 114:=by decide +kernel
  have hfast:StrictAtFast (row 14 114) 14 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 114) 14 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 114) 14 114 hvalid hfast

theorem sr14p115:∀ i ∈ List.range 1,StrictCheckAt 14 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 115) 14 115:=by decide +kernel
  have hfast:StrictAtFast (row 14 115) 14 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 115) 14 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 115) 14 115 hvalid hfast

theorem sr14p116:∀ i ∈ List.range 1,StrictCheckAt 14 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 116) 14 116:=by decide +kernel
  have hfast:StrictAtFast (row 14 116) 14 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 116) 14 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 116) 14 116 hvalid hfast

theorem sr14p117:∀ i ∈ List.range 1,StrictCheckAt 14 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 117) 14 117:=by decide +kernel
  have hfast:StrictAtFast (row 14 117) 14 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 117) 14 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 117) 14 117 hvalid hfast

theorem sr14p118:∀ i ∈ List.range 1,StrictCheckAt 14 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 118) 14 118:=by decide +kernel
  have hfast:StrictAtFast (row 14 118) 14 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 118) 14 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 118) 14 118 hvalid hfast

theorem sr14p119:∀ i ∈ List.range 1,StrictCheckAt 14 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 119) 14 119:=by decide +kernel
  have hfast:StrictAtFast (row 14 119) 14 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 119) 14 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 119) 14 119 hvalid hfast

theorem sr14p120:∀ i ∈ List.range 1,StrictCheckAt 14 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 120) 14 120:=by decide +kernel
  have hfast:StrictAtFast (row 14 120) 14 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 120) 14 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 120) 14 120 hvalid hfast

theorem sr14p121:∀ i ∈ List.range 1,StrictCheckAt 14 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 121) 14 121:=by decide +kernel
  have hfast:StrictAtFast (row 14 121) 14 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 121) 14 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 121) 14 121 hvalid hfast

theorem sr14p122:∀ i ∈ List.range 1,StrictCheckAt 14 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 122) 14 122:=by decide +kernel
  have hfast:StrictAtFast (row 14 122) 14 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 122) 14 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 122) 14 122 hvalid hfast

theorem sr14p123:∀ i ∈ List.range 1,StrictCheckAt 14 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 123) 14 123:=by decide +kernel
  have hfast:StrictAtFast (row 14 123) 14 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 123) 14 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 123) 14 123 hvalid hfast

theorem sr14p124:∀ i ∈ List.range 1,StrictCheckAt 14 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 124) 14 124:=by decide +kernel
  have hfast:StrictAtFast (row 14 124) 14 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 124) 14 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 124) 14 124 hvalid hfast

theorem sr14p125:∀ i ∈ List.range 1,StrictCheckAt 14 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 125) 14 125:=by decide +kernel
  have hfast:StrictAtFast (row 14 125) 14 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 125) 14 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 125) 14 125 hvalid hfast

theorem sr14p126:∀ i ∈ List.range 1,StrictCheckAt 14 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 126) 14 126:=by decide +kernel
  have hfast:StrictAtFast (row 14 126) 14 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 126) 14 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 126) 14 126 hvalid hfast

theorem sr14p127:∀ i ∈ List.range 1,StrictCheckAt 14 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 127) 14 127:=by decide +kernel
  have hfast:StrictAtFast (row 14 127) 14 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 127) 14 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 127) 14 127 hvalid hfast

theorem sr14p128:∀ i ∈ List.range 1,StrictCheckAt 14 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 128) 14 128:=by decide +kernel
  have hfast:StrictAtFast (row 14 128) 14 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 128) 14 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 128) 14 128 hvalid hfast

theorem br14p0:∀ i ∈ List.range 4,BaseCheckAt 14 (0+i):=by decide +kernel

theorem br14p1:∀ i ∈ List.range 4,BaseCheckAt 14 (4+i):=by decide +kernel

theorem br14p2:∀ i ∈ List.range 4,BaseCheckAt 14 (8+i):=by decide +kernel

theorem br14p3:∀ i ∈ List.range 4,BaseCheckAt 14 (12+i):=by decide +kernel

theorem br14p4:∀ i ∈ List.range 4,BaseCheckAt 14 (16+i):=by decide +kernel

theorem br14p5:∀ i ∈ List.range 4,BaseCheckAt 14 (20+i):=by decide +kernel

theorem br14p6:∀ i ∈ List.range 4,BaseCheckAt 14 (24+i):=by decide +kernel

theorem br14p7:∀ i ∈ List.range 4,BaseCheckAt 14 (28+i):=by decide +kernel

theorem br14p8:∀ i ∈ List.range 4,BaseCheckAt 14 (32+i):=by decide +kernel

theorem br14p9:∀ i ∈ List.range 4,BaseCheckAt 14 (36+i):=by decide +kernel

theorem br14p10:∀ i ∈ List.range 4,BaseCheckAt 14 (40+i):=by decide +kernel

theorem br14p11:∀ i ∈ List.range 4,BaseCheckAt 14 (44+i):=by decide +kernel

theorem br14p12:∀ i ∈ List.range 4,BaseCheckAt 14 (48+i):=by decide +kernel

theorem br14p13:∀ i ∈ List.range 4,BaseCheckAt 14 (52+i):=by decide +kernel

theorem br14p14:∀ i ∈ List.range 4,BaseCheckAt 14 (56+i):=by decide +kernel

theorem br14p15:∀ i ∈ List.range 4,BaseCheckAt 14 (60+i):=by decide +kernel



theorem br14p16:∀ i ∈ List.range 4,BaseCheckAt 14 (64+i):=by decide +kernel

theorem br14p17:∀ i ∈ List.range 4,BaseCheckAt 14 (68+i):=by decide +kernel

theorem br14p18:∀ i ∈ List.range 4,BaseCheckAt 14 (72+i):=by decide +kernel

theorem br14p19:∀ i ∈ List.range 4,BaseCheckAt 14 (76+i):=by decide +kernel

theorem br14p20:∀ i ∈ List.range 4,BaseCheckAt 14 (80+i):=by decide +kernel

theorem br14p21:∀ i ∈ List.range 4,BaseCheckAt 14 (84+i):=by decide +kernel

theorem br14p22:∀ i ∈ List.range 4,BaseCheckAt 14 (88+i):=by decide +kernel

theorem br14p23:∀ i ∈ List.range 4,BaseCheckAt 14 (92+i):=by decide +kernel

theorem br14p24:∀ i ∈ List.range 4,BaseCheckAt 14 (96+i):=by decide +kernel

theorem br14p25:∀ i ∈ List.range 4,BaseCheckAt 14 (100+i):=by decide +kernel

theorem br14p26:∀ i ∈ List.range 4,BaseCheckAt 14 (104+i):=by decide +kernel

theorem br14p27:∀ i ∈ List.range 4,BaseCheckAt 14 (108+i):=by decide +kernel

theorem br14p28:∀ i ∈ List.range 4,BaseCheckAt 14 (112+i):=by decide +kernel

theorem br14p29:∀ i ∈ List.range 4,BaseCheckAt 14 (116+i):=by decide +kernel

theorem br14p30:∀ i ∈ List.range 4,BaseCheckAt 14 (120+i):=by decide +kernel

theorem br14p31:∀ i ∈ List.range 4,BaseCheckAt 14 (124+i):=by decide +kernel



theorem br14p32:∀ i ∈ List.range 1,BaseCheckAt 14 (128+i):=by decide +kernel



theorem cr14:∀ V ∈ List.range 129,CorrectAt 14 V:=by
  intro V hV
  have hv:V < 129:=List.mem_range.mp hV
  by_cases h0_17:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr14p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr14p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr14p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr14p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr14p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr14p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr14p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr14p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_17:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr14p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr14p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr14p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr14p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_17:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr14p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr14p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_17:V < 120
        · have h:=cr14p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h15_17:V < 128
          · have h:=cr14p15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=cr14p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem zr14:∀ V ∈ List.range 129,ZeroCheckAt 14 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 14 V (by omega) (by omega) (by omega)
theorem sr14:∀ V ∈ List.range 129,StrictCheckAt 14 V:=by
  intro V hV
  have hv:V < 129:=List.mem_range.mp hV
  by_cases h0_129:V < 64
  · by_cases h0_64:V < 32
    · by_cases h0_32:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have h:=sr14p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
              · have h:=sr14p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
            · by_cases h2_4:V < 3
              · have h:=sr14p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
              · have h:=sr14p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have h:=sr14p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
              · have h:=sr14p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
            · by_cases h6_8:V < 7
              · have h:=sr14p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
              · have h:=sr14p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have h:=sr14p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr14p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
            · by_cases h10_12:V < 11
              · have h:=sr14p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr14p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have h:=sr14p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr14p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
            · by_cases h14_16:V < 15
              · have h:=sr14p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
              · have h:=sr14p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
      · by_cases h16_32:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have h:=sr14p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr14p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
            · by_cases h18_20:V < 19
              · have h:=sr14p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr14p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have h:=sr14p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr14p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr14p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr14p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
        · by_cases h24_32:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr14p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr14p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr14p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr14p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
          · by_cases h28_32:V < 30
            · by_cases h28_30:V < 29
              · have h:=sr14p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr14p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_32:V < 31
              · have h:=sr14p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · have h:=sr14p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
    · by_cases h32_64:V < 48
      · by_cases h32_48:V < 40
        · by_cases h32_40:V < 36
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have h:=sr14p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr14p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
            · by_cases h34_36:V < 35
              · have h:=sr14p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr14p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have h:=sr14p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr14p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
            · by_cases h38_40:V < 39
              · have h:=sr14p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr14p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
        · by_cases h40_48:V < 44
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have h:=sr14p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr14p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
            · by_cases h42_44:V < 43
              · have h:=sr14p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr14p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have h:=sr14p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr14p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
            · by_cases h46_48:V < 47
              · have h:=sr14p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr14p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
      · by_cases h48_64:V < 56
        · by_cases h48_56:V < 52
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have h:=sr14p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr14p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
            · by_cases h50_52:V < 51
              · have h:=sr14p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr14p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have h:=sr14p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr14p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
            · by_cases h54_56:V < 55
              · have h:=sr14p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr14p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
        · by_cases h56_64:V < 60
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have h:=sr14p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr14p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
            · by_cases h58_60:V < 59
              · have h:=sr14p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr14p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
          · by_cases h60_64:V < 62
            · by_cases h60_62:V < 61
              · have h:=sr14p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr14p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
            · by_cases h62_64:V < 63
              · have h:=sr14p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr14p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
  · by_cases h64_129:V < 96
    · by_cases h64_96:V < 80
      · by_cases h64_80:V < 72
        · by_cases h64_72:V < 68
          · by_cases h64_68:V < 66
            · by_cases h64_66:V < 65
              · have h:=sr14p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr14p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
            · by_cases h66_68:V < 67
              · have h:=sr14p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr14p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have h:=sr14p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr14p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
            · by_cases h70_72:V < 71
              · have h:=sr14p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr14p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
        · by_cases h72_80:V < 76
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have h:=sr14p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr14p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
            · by_cases h74_76:V < 75
              · have h:=sr14p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr14p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have h:=sr14p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr14p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
            · by_cases h78_80:V < 79
              · have h:=sr14p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr14p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
      · by_cases h80_96:V < 88
        · by_cases h80_88:V < 84
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have h:=sr14p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr14p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
            · by_cases h82_84:V < 83
              · have h:=sr14p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr14p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have h:=sr14p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr14p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
            · by_cases h86_88:V < 87
              · have h:=sr14p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr14p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
        · by_cases h88_96:V < 92
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have h:=sr14p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr14p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
            · by_cases h90_92:V < 91
              · have h:=sr14p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr14p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
          · by_cases h92_96:V < 94
            · by_cases h92_94:V < 93
              · have h:=sr14p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr14p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
            · by_cases h94_96:V < 95
              · have h:=sr14p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr14p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
    · by_cases h96_129:V < 112
      · by_cases h96_112:V < 104
        · by_cases h96_104:V < 100
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have h:=sr14p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr14p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
            · by_cases h98_100:V < 99
              · have h:=sr14p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr14p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
          · by_cases h100_104:V < 102
            · by_cases h100_102:V < 101
              · have h:=sr14p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr14p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
            · by_cases h102_104:V < 103
              · have h:=sr14p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr14p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
        · by_cases h104_112:V < 108
          · by_cases h104_108:V < 106
            · by_cases h104_106:V < 105
              · have h:=sr14p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr14p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
            · by_cases h106_108:V < 107
              · have h:=sr14p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr14p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have h:=sr14p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr14p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
            · by_cases h110_112:V < 111
              · have h:=sr14p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr14p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
      · by_cases h112_129:V < 120
        · by_cases h112_120:V < 116
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have h:=sr14p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr14p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
            · by_cases h114_116:V < 115
              · have h:=sr14p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr14p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have h:=sr14p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr14p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
            · by_cases h118_120:V < 119
              · have h:=sr14p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr14p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
        · by_cases h120_129:V < 124
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have h:=sr14p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
              · have h:=sr14p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
            · by_cases h122_124:V < 123
              · have h:=sr14p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
              · have h:=sr14p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
          · by_cases h124_129:V < 126
            · by_cases h124_126:V < 125
              · have h:=sr14p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
              · have h:=sr14p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
            · by_cases h126_129:V < 127
              · have h:=sr14p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h
              · by_cases h127_129:V < 128
                · have h:=sr14p127 (V-127) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using h
                · have h:=sr14p128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem br14:∀ V ∈ List.range 129,BaseCheckAt 14 V:=by
  intro V hV
  have hv:V < 129:=List.mem_range.mp hV
  by_cases h0_33:V < 64
  · by_cases h0_16:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br14p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br14p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br14p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br14p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br14p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br14p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br14p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br14p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_16:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br14p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br14p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br14p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br14p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_16:V < 56
        · by_cases h12_14:V < 52
          · have h:=br14p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br14p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_16:V < 60
          · have h:=br14p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · have h:=br14p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h16_33:V < 96
    · by_cases h16_24:V < 80
      · by_cases h16_20:V < 72
        · by_cases h16_18:V < 68
          · have h:=br14p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br14p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h18_20:V < 76
          · have h:=br14p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br14p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h20_24:V < 88
        · by_cases h20_22:V < 84
          · have h:=br14p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br14p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br14p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br14p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h24_33:V < 112
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br14p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br14p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br14p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br14p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h28_33:V < 120
        · by_cases h28_30:V < 116
          · have h:=br14p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br14p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h30_33:V < 124
          · have h:=br14p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · by_cases h31_33:V < 128
            · have h:=br14p31 (V-124) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
            · have h:=br14p32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
