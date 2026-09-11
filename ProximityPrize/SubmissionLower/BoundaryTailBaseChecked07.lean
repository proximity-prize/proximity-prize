import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked06
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastValidated
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr7p0:∀ i ∈ List.range 8,CorrectAt 7 (0+i):=by decide +kernel

theorem cr7p1:∀ i ∈ List.range 8,CorrectAt 7 (8+i):=by decide +kernel

theorem cr7p2:∀ i ∈ List.range 8,CorrectAt 7 (16+i):=by decide +kernel

theorem cr7p3:∀ i ∈ List.range 8,CorrectAt 7 (24+i):=by decide +kernel

theorem cr7p4:∀ i ∈ List.range 8,CorrectAt 7 (32+i):=by decide +kernel

theorem cr7p5:∀ i ∈ List.range 8,CorrectAt 7 (40+i):=by decide +kernel

theorem cr7p6:∀ i ∈ List.range 8,CorrectAt 7 (48+i):=by decide +kernel

theorem cr7p7:∀ i ∈ List.range 8,CorrectAt 7 (56+i):=by decide +kernel

theorem cr7p8:∀ i ∈ List.range 8,CorrectAt 7 (64+i):=by decide +kernel

theorem cr7p9:∀ i ∈ List.range 8,CorrectAt 7 (72+i):=by decide +kernel

theorem cr7p10:∀ i ∈ List.range 8,CorrectAt 7 (80+i):=by decide +kernel

theorem cr7p11:∀ i ∈ List.range 8,CorrectAt 7 (88+i):=by decide +kernel

theorem cr7p12:∀ i ∈ List.range 8,CorrectAt 7 (96+i):=by decide +kernel

theorem cr7p13:∀ i ∈ List.range 8,CorrectAt 7 (104+i):=by decide +kernel

theorem cr7p14:∀ i ∈ List.range 8,CorrectAt 7 (112+i):=by decide +kernel

theorem cr7p15:∀ i ∈ List.range 8,CorrectAt 7 (120+i):=by decide +kernel

theorem cr7p16:∀ i ∈ List.range 8,CorrectAt 7 (128+i):=by decide +kernel

theorem sr7p0:∀ i ∈ List.range 1,StrictCheckAt 7 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 0) 7 0:=by decide +kernel
  have hfast:StrictAtFast (row 7 0) 7 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 0) 7 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 0) 7 0 hvalid hfast

theorem sr7p1:∀ i ∈ List.range 1,StrictCheckAt 7 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 1) 7 1:=by decide +kernel
  have hfast:StrictAtFast (row 7 1) 7 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 1) 7 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 1) 7 1 hvalid hfast

theorem sr7p2:∀ i ∈ List.range 1,StrictCheckAt 7 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 2) 7 2:=by decide +kernel
  have hfast:StrictAtFast (row 7 2) 7 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 2) 7 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 2) 7 2 hvalid hfast

theorem sr7p3:∀ i ∈ List.range 1,StrictCheckAt 7 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 3) 7 3:=by decide +kernel
  have hfast:StrictAtFast (row 7 3) 7 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 3) 7 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 3) 7 3 hvalid hfast

theorem sr7p4:∀ i ∈ List.range 1,StrictCheckAt 7 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 4) 7 4:=by decide +kernel
  have hfast:StrictAtFast (row 7 4) 7 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 4) 7 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 4) 7 4 hvalid hfast

theorem sr7p5:∀ i ∈ List.range 1,StrictCheckAt 7 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 5) 7 5:=by decide +kernel
  have hfast:StrictAtFast (row 7 5) 7 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 5) 7 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 5) 7 5 hvalid hfast

theorem sr7p6:∀ i ∈ List.range 1,StrictCheckAt 7 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 6) 7 6:=by decide +kernel
  have hfast:StrictAtFast (row 7 6) 7 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 6) 7 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 6) 7 6 hvalid hfast

theorem sr7p7:∀ i ∈ List.range 1,StrictCheckAt 7 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 7) 7 7:=by decide +kernel
  have hfast:StrictAtFast (row 7 7) 7 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 7) 7 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 7) 7 7 hvalid hfast

theorem sr7p8:∀ i ∈ List.range 1,StrictCheckAt 7 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 8) 7 8:=by decide +kernel
  have hfast:StrictAtFast (row 7 8) 7 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 8) 7 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 8) 7 8 hvalid hfast

theorem sr7p9:∀ i ∈ List.range 1,StrictCheckAt 7 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 9) 7 9:=by decide +kernel
  have hfast:StrictAtFast (row 7 9) 7 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 9) 7 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 9) 7 9 hvalid hfast

theorem sr7p10:∀ i ∈ List.range 1,StrictCheckAt 7 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 10) 7 10:=by decide +kernel
  have hfast:StrictAtFast (row 7 10) 7 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 10) 7 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 10) 7 10 hvalid hfast

theorem sr7p11:∀ i ∈ List.range 1,StrictCheckAt 7 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 11) 7 11:=by decide +kernel
  have hfast:StrictAtFast (row 7 11) 7 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 11) 7 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 11) 7 11 hvalid hfast

theorem sr7p12:∀ i ∈ List.range 1,StrictCheckAt 7 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 12) 7 12:=by decide +kernel
  have hfast:StrictAtFast (row 7 12) 7 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 12) 7 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 12) 7 12 hvalid hfast

theorem sr7p13:∀ i ∈ List.range 1,StrictCheckAt 7 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 13) 7 13:=by decide +kernel
  have hfast:StrictAtFast (row 7 13) 7 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 13) 7 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 13) 7 13 hvalid hfast

theorem sr7p14:∀ i ∈ List.range 1,StrictCheckAt 7 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 14) 7 14:=by decide +kernel
  have hfast:StrictAtFast (row 7 14) 7 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 14) 7 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 14) 7 14 hvalid hfast

theorem sr7p15:∀ i ∈ List.range 1,StrictCheckAt 7 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 15) 7 15:=by decide +kernel
  have hfast:StrictAtFast (row 7 15) 7 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 15) 7 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 15) 7 15 hvalid hfast

theorem sr7p16:∀ i ∈ List.range 1,StrictCheckAt 7 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 16) 7 16:=by decide +kernel
  have hfast:StrictAtFast (row 7 16) 7 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 16) 7 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 16) 7 16 hvalid hfast

theorem sr7p17:∀ i ∈ List.range 1,StrictCheckAt 7 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 17) 7 17:=by decide +kernel
  have hfast:StrictAtFast (row 7 17) 7 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 17) 7 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 17) 7 17 hvalid hfast

theorem sr7p18:∀ i ∈ List.range 1,StrictCheckAt 7 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 18) 7 18:=by decide +kernel
  have hfast:StrictAtFast (row 7 18) 7 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 18) 7 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 18) 7 18 hvalid hfast

theorem sr7p19:∀ i ∈ List.range 1,StrictCheckAt 7 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 19) 7 19:=by decide +kernel
  have hfast:StrictAtFast (row 7 19) 7 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 19) 7 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 19) 7 19 hvalid hfast

theorem sr7p20:∀ i ∈ List.range 1,StrictCheckAt 7 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 20) 7 20:=by decide +kernel
  have hfast:StrictAtFast (row 7 20) 7 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 20) 7 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 20) 7 20 hvalid hfast

theorem sr7p21:∀ i ∈ List.range 1,StrictCheckAt 7 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 21) 7 21:=by decide +kernel
  have hfast:StrictAtFast (row 7 21) 7 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 21) 7 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 21) 7 21 hvalid hfast

theorem sr7p22:∀ i ∈ List.range 1,StrictCheckAt 7 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 22) 7 22:=by decide +kernel
  have hfast:StrictAtFast (row 7 22) 7 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 22) 7 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 22) 7 22 hvalid hfast

theorem sr7p23:∀ i ∈ List.range 1,StrictCheckAt 7 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 23) 7 23:=by decide +kernel
  have hfast:StrictAtFast (row 7 23) 7 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 23) 7 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 23) 7 23 hvalid hfast

theorem sr7p24:∀ i ∈ List.range 1,StrictCheckAt 7 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 24) 7 24:=by decide +kernel
  have hfast:StrictAtFast (row 7 24) 7 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 24) 7 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 24) 7 24 hvalid hfast

theorem sr7p25:∀ i ∈ List.range 1,StrictCheckAt 7 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 25) 7 25:=by decide +kernel
  have hfast:StrictAtFast (row 7 25) 7 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 25) 7 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 25) 7 25 hvalid hfast

theorem sr7p26:∀ i ∈ List.range 1,StrictCheckAt 7 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 26) 7 26:=by decide +kernel
  have hfast:StrictAtFast (row 7 26) 7 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 26) 7 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 26) 7 26 hvalid hfast

theorem sr7p27:∀ i ∈ List.range 1,StrictCheckAt 7 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 27) 7 27:=by decide +kernel
  have hfast:StrictAtFast (row 7 27) 7 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 27) 7 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 27) 7 27 hvalid hfast

theorem sr7p28:∀ i ∈ List.range 1,StrictCheckAt 7 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 28) 7 28:=by decide +kernel
  have hfast:StrictAtFast (row 7 28) 7 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 28) 7 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 28) 7 28 hvalid hfast

theorem sr7p29:∀ i ∈ List.range 1,StrictCheckAt 7 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 29) 7 29:=by decide +kernel
  have hfast:StrictAtFast (row 7 29) 7 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 29) 7 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 29) 7 29 hvalid hfast

theorem sr7p30:∀ i ∈ List.range 1,StrictCheckAt 7 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 30) 7 30:=by decide +kernel
  have hfast:StrictAtFast (row 7 30) 7 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 30) 7 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 30) 7 30 hvalid hfast

theorem sr7p31:∀ i ∈ List.range 1,StrictCheckAt 7 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 31) 7 31:=by decide +kernel
  have hfast:StrictAtFast (row 7 31) 7 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 31) 7 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 31) 7 31 hvalid hfast

theorem sr7p32:∀ i ∈ List.range 1,StrictCheckAt 7 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 32) 7 32:=by decide +kernel
  have hfast:StrictAtFast (row 7 32) 7 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 32) 7 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 32) 7 32 hvalid hfast

theorem sr7p33:∀ i ∈ List.range 1,StrictCheckAt 7 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 33) 7 33:=by decide +kernel
  have hfast:StrictAtFast (row 7 33) 7 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 33) 7 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 33) 7 33 hvalid hfast

theorem sr7p34:∀ i ∈ List.range 1,StrictCheckAt 7 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 34) 7 34:=by decide +kernel
  have hfast:StrictAtFast (row 7 34) 7 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 34) 7 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 34) 7 34 hvalid hfast

theorem sr7p35:∀ i ∈ List.range 1,StrictCheckAt 7 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 35) 7 35:=by decide +kernel
  have hfast:StrictAtFast (row 7 35) 7 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 35) 7 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 35) 7 35 hvalid hfast

theorem sr7p36:∀ i ∈ List.range 1,StrictCheckAt 7 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 36) 7 36:=by decide +kernel
  have hfast:StrictAtFast (row 7 36) 7 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 36) 7 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 36) 7 36 hvalid hfast

theorem sr7p37:∀ i ∈ List.range 1,StrictCheckAt 7 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 37) 7 37:=by decide +kernel
  have hfast:StrictAtFast (row 7 37) 7 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 37) 7 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 37) 7 37 hvalid hfast

theorem sr7p38:∀ i ∈ List.range 1,StrictCheckAt 7 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 38) 7 38:=by decide +kernel
  have hfast:StrictAtFast (row 7 38) 7 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 38) 7 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 38) 7 38 hvalid hfast

theorem sr7p39:∀ i ∈ List.range 1,StrictCheckAt 7 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 39) 7 39:=by decide +kernel
  have hfast:StrictAtFast (row 7 39) 7 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 39) 7 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 39) 7 39 hvalid hfast

theorem sr7p40:∀ i ∈ List.range 1,StrictCheckAt 7 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 40) 7 40:=by decide +kernel
  have hfast:StrictAtFast (row 7 40) 7 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 40) 7 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 40) 7 40 hvalid hfast

theorem sr7p41:∀ i ∈ List.range 1,StrictCheckAt 7 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 41) 7 41:=by decide +kernel
  have hfast:StrictAtFast (row 7 41) 7 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 41) 7 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 41) 7 41 hvalid hfast

theorem sr7p42:∀ i ∈ List.range 1,StrictCheckAt 7 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 42) 7 42:=by decide +kernel
  have hfast:StrictAtFast (row 7 42) 7 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 42) 7 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 42) 7 42 hvalid hfast

theorem sr7p43:∀ i ∈ List.range 1,StrictCheckAt 7 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 43) 7 43:=by decide +kernel
  have hfast:StrictAtFast (row 7 43) 7 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 43) 7 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 43) 7 43 hvalid hfast

theorem sr7p44:∀ i ∈ List.range 1,StrictCheckAt 7 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 44) 7 44:=by decide +kernel
  have hfast:StrictAtFast (row 7 44) 7 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 44) 7 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 44) 7 44 hvalid hfast

theorem sr7p45:∀ i ∈ List.range 1,StrictCheckAt 7 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 45) 7 45:=by decide +kernel
  have hfast:StrictAtFast (row 7 45) 7 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 45) 7 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 45) 7 45 hvalid hfast

theorem sr7p46:∀ i ∈ List.range 1,StrictCheckAt 7 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 46) 7 46:=by decide +kernel
  have hfast:StrictAtFast (row 7 46) 7 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 46) 7 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 46) 7 46 hvalid hfast

theorem sr7p47:∀ i ∈ List.range 1,StrictCheckAt 7 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 47) 7 47:=by decide +kernel
  have hfast:StrictAtFast (row 7 47) 7 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 47) 7 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 47) 7 47 hvalid hfast

theorem sr7p48:∀ i ∈ List.range 1,StrictCheckAt 7 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 48) 7 48:=by decide +kernel
  have hfast:StrictAtFast (row 7 48) 7 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 48) 7 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 48) 7 48 hvalid hfast

theorem sr7p49:∀ i ∈ List.range 1,StrictCheckAt 7 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 49) 7 49:=by decide +kernel
  have hfast:StrictAtFast (row 7 49) 7 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 49) 7 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 49) 7 49 hvalid hfast

theorem sr7p50:∀ i ∈ List.range 1,StrictCheckAt 7 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 50) 7 50:=by decide +kernel
  have hfast:StrictAtFast (row 7 50) 7 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 50) 7 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 50) 7 50 hvalid hfast

theorem sr7p51:∀ i ∈ List.range 1,StrictCheckAt 7 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 51) 7 51:=by decide +kernel
  have hfast:StrictAtFast (row 7 51) 7 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 51) 7 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 51) 7 51 hvalid hfast

theorem sr7p52:∀ i ∈ List.range 1,StrictCheckAt 7 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 52) 7 52:=by decide +kernel
  have hfast:StrictAtFast (row 7 52) 7 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 52) 7 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 52) 7 52 hvalid hfast

theorem sr7p53:∀ i ∈ List.range 1,StrictCheckAt 7 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 53) 7 53:=by decide +kernel
  have hfast:StrictAtFast (row 7 53) 7 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 53) 7 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 53) 7 53 hvalid hfast

theorem sr7p54:∀ i ∈ List.range 1,StrictCheckAt 7 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 54) 7 54:=by decide +kernel
  have hfast:StrictAtFast (row 7 54) 7 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 54) 7 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 54) 7 54 hvalid hfast

theorem sr7p55:∀ i ∈ List.range 1,StrictCheckAt 7 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 55) 7 55:=by decide +kernel
  have hfast:StrictAtFast (row 7 55) 7 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 55) 7 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 55) 7 55 hvalid hfast

theorem sr7p56:∀ i ∈ List.range 1,StrictCheckAt 7 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 56) 7 56:=by decide +kernel
  have hfast:StrictAtFast (row 7 56) 7 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 56) 7 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 56) 7 56 hvalid hfast

theorem sr7p57:∀ i ∈ List.range 1,StrictCheckAt 7 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 57) 7 57:=by decide +kernel
  have hfast:StrictAtFast (row 7 57) 7 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 57) 7 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 57) 7 57 hvalid hfast

theorem sr7p58:∀ i ∈ List.range 1,StrictCheckAt 7 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 58) 7 58:=by decide +kernel
  have hfast:StrictAtFast (row 7 58) 7 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 58) 7 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 58) 7 58 hvalid hfast

theorem sr7p59:∀ i ∈ List.range 1,StrictCheckAt 7 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 59) 7 59:=by decide +kernel
  have hfast:StrictAtFast (row 7 59) 7 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 59) 7 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 59) 7 59 hvalid hfast

theorem sr7p60:∀ i ∈ List.range 1,StrictCheckAt 7 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 60) 7 60:=by decide +kernel
  have hfast:StrictAtFast (row 7 60) 7 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 60) 7 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 60) 7 60 hvalid hfast

theorem sr7p61:∀ i ∈ List.range 1,StrictCheckAt 7 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 61) 7 61:=by decide +kernel
  have hfast:StrictAtFast (row 7 61) 7 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 61) 7 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 61) 7 61 hvalid hfast

theorem sr7p62:∀ i ∈ List.range 1,StrictCheckAt 7 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 62) 7 62:=by decide +kernel
  have hfast:StrictAtFast (row 7 62) 7 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 62) 7 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 62) 7 62 hvalid hfast

theorem sr7p63:∀ i ∈ List.range 1,StrictCheckAt 7 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 63) 7 63:=by decide +kernel
  have hfast:StrictAtFast (row 7 63) 7 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 63) 7 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 63) 7 63 hvalid hfast

theorem sr7p64:∀ i ∈ List.range 1,StrictCheckAt 7 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 64) 7 64:=by decide +kernel
  have hfast:StrictAtFast (row 7 64) 7 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 64) 7 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 64) 7 64 hvalid hfast

theorem sr7p65:∀ i ∈ List.range 1,StrictCheckAt 7 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 65) 7 65:=by decide +kernel
  have hfast:StrictAtFast (row 7 65) 7 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 65) 7 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 65) 7 65 hvalid hfast

theorem sr7p66:∀ i ∈ List.range 1,StrictCheckAt 7 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 66) 7 66:=by decide +kernel
  have hfast:StrictAtFast (row 7 66) 7 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 66) 7 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 66) 7 66 hvalid hfast

theorem sr7p67:∀ i ∈ List.range 1,StrictCheckAt 7 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 67) 7 67:=by decide +kernel
  have hfast:StrictAtFast (row 7 67) 7 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 67) 7 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 67) 7 67 hvalid hfast

theorem sr7p68:∀ i ∈ List.range 1,StrictCheckAt 7 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 68) 7 68:=by decide +kernel
  have hfast:StrictAtFast (row 7 68) 7 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 68) 7 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 68) 7 68 hvalid hfast

theorem sr7p69:∀ i ∈ List.range 1,StrictCheckAt 7 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 69) 7 69:=by decide +kernel
  have hfast:StrictAtFast (row 7 69) 7 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 69) 7 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 69) 7 69 hvalid hfast

theorem sr7p70:∀ i ∈ List.range 1,StrictCheckAt 7 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 70) 7 70:=by decide +kernel
  have hfast:StrictAtFast (row 7 70) 7 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 70) 7 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 70) 7 70 hvalid hfast

theorem sr7p71:∀ i ∈ List.range 1,StrictCheckAt 7 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 71) 7 71:=by decide +kernel
  have hfast:StrictAtFast (row 7 71) 7 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 71) 7 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 71) 7 71 hvalid hfast

theorem sr7p72:∀ i ∈ List.range 1,StrictCheckAt 7 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 72) 7 72:=by decide +kernel
  have hfast:StrictAtFast (row 7 72) 7 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 72) 7 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 72) 7 72 hvalid hfast

theorem sr7p73:∀ i ∈ List.range 1,StrictCheckAt 7 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 73) 7 73:=by decide +kernel
  have hfast:StrictAtFast (row 7 73) 7 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 73) 7 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 73) 7 73 hvalid hfast

theorem sr7p74:∀ i ∈ List.range 1,StrictCheckAt 7 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 74) 7 74:=by decide +kernel
  have hfast:StrictAtFast (row 7 74) 7 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 74) 7 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 74) 7 74 hvalid hfast

theorem sr7p75:∀ i ∈ List.range 1,StrictCheckAt 7 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 75) 7 75:=by decide +kernel
  have hfast:StrictAtFast (row 7 75) 7 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 75) 7 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 75) 7 75 hvalid hfast

theorem sr7p76:∀ i ∈ List.range 1,StrictCheckAt 7 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 76) 7 76:=by decide +kernel
  have hfast:StrictAtFast (row 7 76) 7 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 76) 7 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 76) 7 76 hvalid hfast

theorem sr7p77:∀ i ∈ List.range 1,StrictCheckAt 7 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 77) 7 77:=by decide +kernel
  have hfast:StrictAtFast (row 7 77) 7 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 77) 7 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 77) 7 77 hvalid hfast

theorem sr7p78:∀ i ∈ List.range 1,StrictCheckAt 7 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 78) 7 78:=by decide +kernel
  have hfast:StrictAtFast (row 7 78) 7 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 78) 7 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 78) 7 78 hvalid hfast

theorem sr7p79:∀ i ∈ List.range 1,StrictCheckAt 7 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 79) 7 79:=by decide +kernel
  have hfast:StrictAtFast (row 7 79) 7 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 79) 7 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 79) 7 79 hvalid hfast

theorem sr7p80:∀ i ∈ List.range 1,StrictCheckAt 7 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 80) 7 80:=by decide +kernel
  have hfast:StrictAtFast (row 7 80) 7 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 80) 7 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 80) 7 80 hvalid hfast

theorem sr7p81:∀ i ∈ List.range 1,StrictCheckAt 7 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 81) 7 81:=by decide +kernel
  have hfast:StrictAtFast (row 7 81) 7 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 81) 7 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 81) 7 81 hvalid hfast

theorem sr7p82:∀ i ∈ List.range 1,StrictCheckAt 7 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 82) 7 82:=by decide +kernel
  have hfast:StrictAtFast (row 7 82) 7 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 82) 7 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 82) 7 82 hvalid hfast

theorem sr7p83:∀ i ∈ List.range 1,StrictCheckAt 7 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 83) 7 83:=by decide +kernel
  have hfast:StrictAtFast (row 7 83) 7 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 83) 7 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 83) 7 83 hvalid hfast

theorem sr7p84:∀ i ∈ List.range 1,StrictCheckAt 7 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 84) 7 84:=by decide +kernel
  have hfast:StrictAtFast (row 7 84) 7 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 84) 7 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 84) 7 84 hvalid hfast

theorem sr7p85:∀ i ∈ List.range 1,StrictCheckAt 7 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 85) 7 85:=by decide +kernel
  have hfast:StrictAtFast (row 7 85) 7 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 85) 7 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 85) 7 85 hvalid hfast

theorem sr7p86:∀ i ∈ List.range 1,StrictCheckAt 7 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 86) 7 86:=by decide +kernel
  have hfast:StrictAtFast (row 7 86) 7 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 86) 7 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 86) 7 86 hvalid hfast

theorem sr7p87:∀ i ∈ List.range 1,StrictCheckAt 7 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 87) 7 87:=by decide +kernel
  have hfast:StrictAtFast (row 7 87) 7 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 87) 7 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 87) 7 87 hvalid hfast

theorem sr7p88:∀ i ∈ List.range 1,StrictCheckAt 7 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 88) 7 88:=by decide +kernel
  have hfast:StrictAtFast (row 7 88) 7 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 88) 7 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 88) 7 88 hvalid hfast

theorem sr7p89:∀ i ∈ List.range 1,StrictCheckAt 7 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 89) 7 89:=by decide +kernel
  have hfast:StrictAtFast (row 7 89) 7 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 89) 7 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 89) 7 89 hvalid hfast

theorem sr7p90:∀ i ∈ List.range 1,StrictCheckAt 7 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 90) 7 90:=by decide +kernel
  have hfast:StrictAtFast (row 7 90) 7 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 90) 7 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 90) 7 90 hvalid hfast

theorem sr7p91:∀ i ∈ List.range 1,StrictCheckAt 7 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 91) 7 91:=by decide +kernel
  have hfast:StrictAtFast (row 7 91) 7 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 91) 7 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 91) 7 91 hvalid hfast

theorem sr7p92:∀ i ∈ List.range 1,StrictCheckAt 7 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 92) 7 92:=by decide +kernel
  have hfast:StrictAtFast (row 7 92) 7 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 92) 7 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 92) 7 92 hvalid hfast

theorem sr7p93:∀ i ∈ List.range 1,StrictCheckAt 7 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 93) 7 93:=by decide +kernel
  have hfast:StrictAtFast (row 7 93) 7 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 93) 7 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 93) 7 93 hvalid hfast

theorem sr7p94:∀ i ∈ List.range 1,StrictCheckAt 7 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 94) 7 94:=by decide +kernel
  have hfast:StrictAtFast (row 7 94) 7 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 94) 7 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 94) 7 94 hvalid hfast

theorem sr7p95:∀ i ∈ List.range 1,StrictCheckAt 7 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 95) 7 95:=by decide +kernel
  have hfast:StrictAtFast (row 7 95) 7 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 95) 7 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 95) 7 95 hvalid hfast

theorem sr7p96:∀ i ∈ List.range 1,StrictCheckAt 7 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 96) 7 96:=by decide +kernel
  have hfast:StrictAtFast (row 7 96) 7 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 96) 7 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 96) 7 96 hvalid hfast

theorem sr7p97:∀ i ∈ List.range 1,StrictCheckAt 7 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 97) 7 97:=by decide +kernel
  have hfast:StrictAtFast (row 7 97) 7 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 97) 7 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 97) 7 97 hvalid hfast

theorem sr7p98:∀ i ∈ List.range 1,StrictCheckAt 7 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 98) 7 98:=by decide +kernel
  have hfast:StrictAtFast (row 7 98) 7 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 98) 7 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 98) 7 98 hvalid hfast

theorem sr7p99:∀ i ∈ List.range 1,StrictCheckAt 7 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 99) 7 99:=by decide +kernel
  have hfast:StrictAtFast (row 7 99) 7 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 99) 7 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 99) 7 99 hvalid hfast

theorem sr7p100:∀ i ∈ List.range 1,StrictCheckAt 7 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 100) 7 100:=by decide +kernel
  have hfast:StrictAtFast (row 7 100) 7 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 100) 7 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 100) 7 100 hvalid hfast

theorem sr7p101:∀ i ∈ List.range 1,StrictCheckAt 7 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 101) 7 101:=by decide +kernel
  have hfast:StrictAtFast (row 7 101) 7 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 101) 7 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 101) 7 101 hvalid hfast

theorem sr7p102:∀ i ∈ List.range 1,StrictCheckAt 7 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 102) 7 102:=by decide +kernel
  have hfast:StrictAtFast (row 7 102) 7 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 102) 7 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 102) 7 102 hvalid hfast

theorem sr7p103:∀ i ∈ List.range 1,StrictCheckAt 7 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 103) 7 103:=by decide +kernel
  have hfast:StrictAtFast (row 7 103) 7 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 103) 7 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 103) 7 103 hvalid hfast

theorem sr7p104:∀ i ∈ List.range 1,StrictCheckAt 7 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 104) 7 104:=by decide +kernel
  have hfast:StrictAtFast (row 7 104) 7 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 104) 7 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 104) 7 104 hvalid hfast

theorem sr7p105:∀ i ∈ List.range 1,StrictCheckAt 7 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 105) 7 105:=by decide +kernel
  have hfast:StrictAtFast (row 7 105) 7 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 105) 7 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 105) 7 105 hvalid hfast

theorem sr7p106:∀ i ∈ List.range 1,StrictCheckAt 7 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 106) 7 106:=by decide +kernel
  have hfast:StrictAtFast (row 7 106) 7 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 106) 7 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 106) 7 106 hvalid hfast

theorem sr7p107:∀ i ∈ List.range 1,StrictCheckAt 7 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 107) 7 107:=by decide +kernel
  have hfast:StrictAtFast (row 7 107) 7 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 107) 7 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 107) 7 107 hvalid hfast

theorem sr7p108:∀ i ∈ List.range 1,StrictCheckAt 7 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 108) 7 108:=by decide +kernel
  have hfast:StrictAtFast (row 7 108) 7 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 108) 7 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 108) 7 108 hvalid hfast

theorem sr7p109:∀ i ∈ List.range 1,StrictCheckAt 7 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 109) 7 109:=by decide +kernel
  have hfast:StrictAtFast (row 7 109) 7 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 109) 7 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 109) 7 109 hvalid hfast

theorem sr7p110:∀ i ∈ List.range 1,StrictCheckAt 7 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 110) 7 110:=by decide +kernel
  have hfast:StrictAtFast (row 7 110) 7 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 110) 7 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 110) 7 110 hvalid hfast

theorem sr7p111:∀ i ∈ List.range 1,StrictCheckAt 7 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 111) 7 111:=by decide +kernel
  have hfast:StrictAtFast (row 7 111) 7 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 111) 7 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 111) 7 111 hvalid hfast

theorem sr7p112:∀ i ∈ List.range 1,StrictCheckAt 7 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 112) 7 112:=by decide +kernel
  have hfast:StrictAtFast (row 7 112) 7 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 112) 7 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 112) 7 112 hvalid hfast

theorem sr7p113:∀ i ∈ List.range 1,StrictCheckAt 7 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 113) 7 113:=by decide +kernel
  have hfast:StrictAtFast (row 7 113) 7 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 113) 7 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 113) 7 113 hvalid hfast

theorem sr7p114:∀ i ∈ List.range 1,StrictCheckAt 7 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 114) 7 114:=by decide +kernel
  have hfast:StrictAtFast (row 7 114) 7 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 114) 7 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 114) 7 114 hvalid hfast

theorem sr7p115:∀ i ∈ List.range 1,StrictCheckAt 7 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 115) 7 115:=by decide +kernel
  have hfast:StrictAtFast (row 7 115) 7 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 115) 7 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 115) 7 115 hvalid hfast

theorem sr7p116:∀ i ∈ List.range 1,StrictCheckAt 7 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 116) 7 116:=by decide +kernel
  have hfast:StrictAtFast (row 7 116) 7 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 116) 7 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 116) 7 116 hvalid hfast

theorem sr7p117:∀ i ∈ List.range 1,StrictCheckAt 7 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 117) 7 117:=by decide +kernel
  have hfast:StrictAtFast (row 7 117) 7 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 117) 7 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 117) 7 117 hvalid hfast

theorem sr7p118:∀ i ∈ List.range 1,StrictCheckAt 7 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 118) 7 118:=by decide +kernel
  have hfast:StrictAtFast (row 7 118) 7 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 118) 7 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 118) 7 118 hvalid hfast

theorem sr7p119:∀ i ∈ List.range 1,StrictCheckAt 7 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 119) 7 119:=by decide +kernel
  have hfast:StrictAtFast (row 7 119) 7 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 119) 7 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 119) 7 119 hvalid hfast

theorem sr7p120:∀ i ∈ List.range 1,StrictCheckAt 7 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 120) 7 120:=by decide +kernel
  have hfast:StrictAtFast (row 7 120) 7 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 120) 7 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 120) 7 120 hvalid hfast

theorem sr7p121:∀ i ∈ List.range 1,StrictCheckAt 7 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 121) 7 121:=by decide +kernel
  have hfast:StrictAtFast (row 7 121) 7 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 121) 7 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 121) 7 121 hvalid hfast

theorem sr7p122:∀ i ∈ List.range 1,StrictCheckAt 7 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 122) 7 122:=by decide +kernel
  have hfast:StrictAtFast (row 7 122) 7 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 122) 7 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 122) 7 122 hvalid hfast

theorem sr7p123:∀ i ∈ List.range 1,StrictCheckAt 7 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 123) 7 123:=by decide +kernel
  have hfast:StrictAtFast (row 7 123) 7 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 123) 7 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 123) 7 123 hvalid hfast

theorem sr7p124:∀ i ∈ List.range 1,StrictCheckAt 7 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 124) 7 124:=by decide +kernel
  have hfast:StrictAtFast (row 7 124) 7 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 124) 7 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 124) 7 124 hvalid hfast

theorem sr7p125:∀ i ∈ List.range 1,StrictCheckAt 7 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 125) 7 125:=by decide +kernel
  have hfast:StrictAtFast (row 7 125) 7 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 125) 7 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 125) 7 125 hvalid hfast

theorem sr7p126:∀ i ∈ List.range 1,StrictCheckAt 7 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 126) 7 126:=by decide +kernel
  have hfast:StrictAtFast (row 7 126) 7 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 126) 7 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 126) 7 126 hvalid hfast

theorem sr7p127:∀ i ∈ List.range 1,StrictCheckAt 7 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 127) 7 127:=by decide +kernel
  have hfast:StrictAtFast (row 7 127) 7 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 127) 7 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 127) 7 127 hvalid hfast

theorem sr7p128:∀ i ∈ List.range 1,StrictCheckAt 7 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 128) 7 128:=by decide +kernel
  have hfast:StrictAtFast (row 7 128) 7 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 128) 7 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 128) 7 128 hvalid hfast

theorem sr7p129:∀ i ∈ List.range 1,StrictCheckAt 7 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 129) 7 129:=by decide +kernel
  have hfast:StrictAtFast (row 7 129) 7 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 129) 7 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 129) 7 129 hvalid hfast

theorem sr7p130:∀ i ∈ List.range 1,StrictCheckAt 7 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 130) 7 130:=by decide +kernel
  have hfast:StrictAtFast (row 7 130) 7 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 130) 7 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 130) 7 130 hvalid hfast

theorem sr7p131:∀ i ∈ List.range 1,StrictCheckAt 7 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 131 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 131) 7 131:=by decide +kernel
  have hfast:StrictAtFast (row 7 131) 7 131:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 131) 7 131 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 131) 7 131 hvalid hfast

theorem sr7p132:∀ i ∈ List.range 1,StrictCheckAt 7 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 132 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 132) 7 132:=by decide +kernel
  have hfast:StrictAtFast (row 7 132) 7 132:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 132) 7 132 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 132) 7 132 hvalid hfast

theorem sr7p133:∀ i ∈ List.range 1,StrictCheckAt 7 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 133 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 133) 7 133:=by decide +kernel
  have hfast:StrictAtFast (row 7 133) 7 133:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 133) 7 133 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 133) 7 133 hvalid hfast

theorem sr7p134:∀ i ∈ List.range 1,StrictCheckAt 7 (134+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 134 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 134) 7 134:=by decide +kernel
  have hfast:StrictAtFast (row 7 134) 7 134:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 134) 7 134 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 134) 7 134 hvalid hfast

theorem sr7p135:∀ i ∈ List.range 1,StrictCheckAt 7 (135+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 135 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 135) 7 135:=by decide +kernel
  have hfast:StrictAtFast (row 7 135) 7 135:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 135) 7 135 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 135) 7 135 hvalid hfast

theorem br7p0:∀ i ∈ List.range 4,BaseCheckAt 7 (0+i):=by decide +kernel

theorem br7p1:∀ i ∈ List.range 4,BaseCheckAt 7 (4+i):=by decide +kernel

theorem br7p2:∀ i ∈ List.range 4,BaseCheckAt 7 (8+i):=by decide +kernel

theorem br7p3:∀ i ∈ List.range 4,BaseCheckAt 7 (12+i):=by decide +kernel

theorem br7p4:∀ i ∈ List.range 4,BaseCheckAt 7 (16+i):=by decide +kernel

theorem br7p5:∀ i ∈ List.range 4,BaseCheckAt 7 (20+i):=by decide +kernel

theorem br7p6:∀ i ∈ List.range 4,BaseCheckAt 7 (24+i):=by decide +kernel

theorem br7p7:∀ i ∈ List.range 4,BaseCheckAt 7 (28+i):=by decide +kernel

theorem br7p8:∀ i ∈ List.range 4,BaseCheckAt 7 (32+i):=by decide +kernel

theorem br7p9:∀ i ∈ List.range 4,BaseCheckAt 7 (36+i):=by decide +kernel

theorem br7p10:∀ i ∈ List.range 4,BaseCheckAt 7 (40+i):=by decide +kernel

theorem br7p11:∀ i ∈ List.range 4,BaseCheckAt 7 (44+i):=by decide +kernel

theorem br7p12:∀ i ∈ List.range 4,BaseCheckAt 7 (48+i):=by decide +kernel

theorem br7p13:∀ i ∈ List.range 4,BaseCheckAt 7 (52+i):=by decide +kernel

theorem br7p14:∀ i ∈ List.range 4,BaseCheckAt 7 (56+i):=by decide +kernel

theorem br7p15:∀ i ∈ List.range 4,BaseCheckAt 7 (60+i):=by decide +kernel



theorem br7p16:∀ i ∈ List.range 4,BaseCheckAt 7 (64+i):=by decide +kernel

theorem br7p17:∀ i ∈ List.range 4,BaseCheckAt 7 (68+i):=by decide +kernel

theorem br7p18:∀ i ∈ List.range 4,BaseCheckAt 7 (72+i):=by decide +kernel

theorem br7p19:∀ i ∈ List.range 4,BaseCheckAt 7 (76+i):=by decide +kernel

theorem br7p20:∀ i ∈ List.range 4,BaseCheckAt 7 (80+i):=by decide +kernel

theorem br7p21:∀ i ∈ List.range 4,BaseCheckAt 7 (84+i):=by decide +kernel

theorem br7p22:∀ i ∈ List.range 4,BaseCheckAt 7 (88+i):=by decide +kernel

theorem br7p23:∀ i ∈ List.range 4,BaseCheckAt 7 (92+i):=by decide +kernel

theorem br7p24:∀ i ∈ List.range 4,BaseCheckAt 7 (96+i):=by decide +kernel

theorem br7p25:∀ i ∈ List.range 4,BaseCheckAt 7 (100+i):=by decide +kernel

theorem br7p26:∀ i ∈ List.range 4,BaseCheckAt 7 (104+i):=by decide +kernel

theorem br7p27:∀ i ∈ List.range 4,BaseCheckAt 7 (108+i):=by decide +kernel

theorem br7p28:∀ i ∈ List.range 4,BaseCheckAt 7 (112+i):=by decide +kernel

theorem br7p29:∀ i ∈ List.range 4,BaseCheckAt 7 (116+i):=by decide +kernel

theorem br7p30:∀ i ∈ List.range 4,BaseCheckAt 7 (120+i):=by decide +kernel

theorem br7p31:∀ i ∈ List.range 4,BaseCheckAt 7 (124+i):=by decide +kernel



theorem br7p32:∀ i ∈ List.range 4,BaseCheckAt 7 (128+i):=by decide +kernel

theorem br7p33:∀ i ∈ List.range 4,BaseCheckAt 7 (132+i):=by decide +kernel



theorem cr7:∀ V ∈ List.range 136,CorrectAt 7 V:=by
  intro V hV
  have hv:V < 136:=List.mem_range.mp hV
  by_cases h0_17:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr7p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr7p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr7p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr7p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr7p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr7p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr7p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr7p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_17:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr7p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr7p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr7p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr7p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_17:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr7p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr7p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_17:V < 120
        · have h:=cr7p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h15_17:V < 128
          · have h:=cr7p15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=cr7p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem zr7:∀ V ∈ List.range 136,ZeroCheckAt 7 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 7 V (by omega) (by omega) (by omega)
theorem sr7:∀ V ∈ List.range 136,StrictCheckAt 7 V:=by
  intro V hV
  have hv:V < 136:=List.mem_range.mp hV
  by_cases h0_136:V < 68
  · by_cases h0_68:V < 34
    · by_cases h0_34:V < 17
      · by_cases h0_17:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have h:=sr7p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
              · have h:=sr7p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
            · by_cases h2_4:V < 3
              · have h:=sr7p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
              · have h:=sr7p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have h:=sr7p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
              · have h:=sr7p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
            · by_cases h6_8:V < 7
              · have h:=sr7p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
              · have h:=sr7p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
        · by_cases h8_17:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have h:=sr7p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr7p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
            · by_cases h10_12:V < 11
              · have h:=sr7p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr7p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
          · by_cases h12_17:V < 14
            · by_cases h12_14:V < 13
              · have h:=sr7p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr7p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
            · by_cases h14_17:V < 15
              · have h:=sr7p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
              · by_cases h15_17:V < 16
                · have h:=sr7p15 (V-15) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
                · have h:=sr7p16 (V-16) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
      · by_cases h17_34:V < 25
        · by_cases h17_25:V < 21
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr7p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr7p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr7p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr7p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have h:=sr7p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr7p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
            · by_cases h23_25:V < 24
              · have h:=sr7p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr7p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · by_cases h25_34:V < 29
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have h:=sr7p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr7p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
            · by_cases h27_29:V < 28
              · have h:=sr7p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr7p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · by_cases h29_34:V < 31
            · by_cases h29_31:V < 30
              · have h:=sr7p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr7p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
            · by_cases h31_34:V < 32
              · have h:=sr7p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · by_cases h32_34:V < 33
                · have h:=sr7p32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
                · have h:=sr7p33 (V-33) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
    · by_cases h34_68:V < 51
      · by_cases h34_51:V < 42
        · by_cases h34_42:V < 38
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have h:=sr7p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr7p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
            · by_cases h36_38:V < 37
              · have h:=sr7p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr7p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have h:=sr7p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr7p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
            · by_cases h40_42:V < 41
              · have h:=sr7p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr7p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
        · by_cases h42_51:V < 46
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have h:=sr7p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr7p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
            · by_cases h44_46:V < 45
              · have h:=sr7p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr7p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
          · by_cases h46_51:V < 48
            · by_cases h46_48:V < 47
              · have h:=sr7p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr7p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
            · by_cases h48_51:V < 49
              · have h:=sr7p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · by_cases h49_51:V < 50
                · have h:=sr7p49 (V-49) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
                · have h:=sr7p50 (V-50) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
      · by_cases h51_68:V < 59
        · by_cases h51_59:V < 55
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have h:=sr7p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr7p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
            · by_cases h53_55:V < 54
              · have h:=sr7p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr7p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have h:=sr7p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr7p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
            · by_cases h57_59:V < 58
              · have h:=sr7p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr7p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
        · by_cases h59_68:V < 63
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have h:=sr7p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr7p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · by_cases h61_63:V < 62
              · have h:=sr7p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr7p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
          · by_cases h63_68:V < 65
            · by_cases h63_65:V < 64
              · have h:=sr7p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr7p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
            · by_cases h65_68:V < 66
              · have h:=sr7p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · by_cases h66_68:V < 67
                · have h:=sr7p66 (V-66) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
                · have h:=sr7p67 (V-67) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
  · by_cases h68_136:V < 102
    · by_cases h68_102:V < 85
      · by_cases h68_85:V < 76
        · by_cases h68_76:V < 72
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have h:=sr7p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr7p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
            · by_cases h70_72:V < 71
              · have h:=sr7p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr7p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have h:=sr7p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr7p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
            · by_cases h74_76:V < 75
              · have h:=sr7p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr7p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
        · by_cases h76_85:V < 80
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have h:=sr7p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr7p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
            · by_cases h78_80:V < 79
              · have h:=sr7p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr7p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
          · by_cases h80_85:V < 82
            · by_cases h80_82:V < 81
              · have h:=sr7p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr7p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
            · by_cases h82_85:V < 83
              · have h:=sr7p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · by_cases h83_85:V < 84
                · have h:=sr7p83 (V-83) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
                · have h:=sr7p84 (V-84) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
      · by_cases h85_102:V < 93
        · by_cases h85_93:V < 89
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have h:=sr7p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr7p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
            · by_cases h87_89:V < 88
              · have h:=sr7p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr7p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have h:=sr7p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr7p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr7p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr7p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
        · by_cases h93_102:V < 97
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have h:=sr7p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr7p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
            · by_cases h95_97:V < 96
              · have h:=sr7p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr7p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · by_cases h97_102:V < 99
            · by_cases h97_99:V < 98
              · have h:=sr7p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr7p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_102:V < 100
              · have h:=sr7p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · by_cases h100_102:V < 101
                · have h:=sr7p100 (V-100) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
                · have h:=sr7p101 (V-101) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
    · by_cases h102_136:V < 119
      · by_cases h102_119:V < 110
        · by_cases h102_110:V < 106
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have h:=sr7p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr7p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
            · by_cases h104_106:V < 105
              · have h:=sr7p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr7p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have h:=sr7p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr7p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
            · by_cases h108_110:V < 109
              · have h:=sr7p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr7p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
        · by_cases h110_119:V < 114
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have h:=sr7p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr7p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
            · by_cases h112_114:V < 113
              · have h:=sr7p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr7p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
          · by_cases h114_119:V < 116
            · by_cases h114_116:V < 115
              · have h:=sr7p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr7p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
            · by_cases h116_119:V < 117
              · have h:=sr7p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · by_cases h117_119:V < 118
                · have h:=sr7p117 (V-117) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
                · have h:=sr7p118 (V-118) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
      · by_cases h119_136:V < 127
        · by_cases h119_127:V < 123
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have h:=sr7p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
              · have h:=sr7p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
            · by_cases h121_123:V < 122
              · have h:=sr7p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
              · have h:=sr7p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
          · by_cases h123_127:V < 125
            · by_cases h123_125:V < 124
              · have h:=sr7p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
              · have h:=sr7p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
            · by_cases h125_127:V < 126
              · have h:=sr7p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
              · have h:=sr7p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h
        · by_cases h127_136:V < 131
          · by_cases h127_131:V < 129
            · by_cases h127_129:V < 128
              · have h:=sr7p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using h
              · have h:=sr7p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
            · by_cases h129_131:V < 130
              · have h:=sr7p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using h
              · have h:=sr7p130 (V-130) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using h
          · by_cases h131_136:V < 133
            · by_cases h131_133:V < 132
              · have h:=sr7p131 (V-131) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using h
              · have h:=sr7p132 (V-132) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using h
            · by_cases h133_136:V < 134
              · have h:=sr7p133 (V-133) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 133 ≤ V by omega)] using h
              · by_cases h134_136:V < 135
                · have h:=sr7p134 (V-134) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 134 ≤ V by omega)] using h
                · have h:=sr7p135 (V-135) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 135 ≤ V by omega)] using h

theorem br7:∀ V ∈ List.range 136,BaseCheckAt 7 V:=by
  intro V hV
  have hv:V < 136:=List.mem_range.mp hV
  by_cases h0_34:V < 68
  · by_cases h0_17:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br7p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br7p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br7p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br7p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br7p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br7p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br7p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br7p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_17:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br7p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br7p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br7p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br7p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_17:V < 56
        · by_cases h12_14:V < 52
          · have h:=br7p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br7p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_17:V < 60
          · have h:=br7p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · by_cases h15_17:V < 64
            · have h:=br7p15 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · have h:=br7p16 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
  · by_cases h17_34:V < 100
    · by_cases h17_25:V < 84
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br7p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br7p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br7p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br7p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
      · by_cases h21_25:V < 92
        · by_cases h21_23:V < 88
          · have h:=br7p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br7p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h23_25:V < 96
          · have h:=br7p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br7p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
    · by_cases h25_34:V < 116
      · by_cases h25_29:V < 108
        · by_cases h25_27:V < 104
          · have h:=br7p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br7p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h27_29:V < 112
          · have h:=br7p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br7p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
      · by_cases h29_34:V < 124
        · by_cases h29_31:V < 120
          · have h:=br7p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · have h:=br7p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
        · by_cases h31_34:V < 128
          · have h:=br7p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
          · by_cases h32_34:V < 132
            · have h:=br7p32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
            · have h:=br7p33 (V-132) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 132 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
