import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr12p0:∀ i ∈ List.range 8,CorrectAt 12 (0+i):=by decide +kernel

theorem cr12p1:∀ i ∈ List.range 8,CorrectAt 12 (8+i):=by decide +kernel

theorem cr12p2:∀ i ∈ List.range 8,CorrectAt 12 (16+i):=by decide +kernel

theorem cr12p3:∀ i ∈ List.range 8,CorrectAt 12 (24+i):=by decide +kernel

theorem cr12p4:∀ i ∈ List.range 8,CorrectAt 12 (32+i):=by decide +kernel

theorem cr12p5:∀ i ∈ List.range 8,CorrectAt 12 (40+i):=by decide +kernel

theorem cr12p6:∀ i ∈ List.range 8,CorrectAt 12 (48+i):=by decide +kernel

theorem cr12p7:∀ i ∈ List.range 8,CorrectAt 12 (56+i):=by decide +kernel

theorem cr12p8:∀ i ∈ List.range 8,CorrectAt 12 (64+i):=by decide +kernel

theorem cr12p9:∀ i ∈ List.range 8,CorrectAt 12 (72+i):=by decide +kernel

theorem cr12p10:∀ i ∈ List.range 8,CorrectAt 12 (80+i):=by decide +kernel

theorem cr12p11:∀ i ∈ List.range 8,CorrectAt 12 (88+i):=by decide +kernel

theorem cr12p12:∀ i ∈ List.range 8,CorrectAt 12 (96+i):=by decide +kernel

theorem cr12p13:∀ i ∈ List.range 8,CorrectAt 12 (104+i):=by decide +kernel

theorem cr12p14:∀ i ∈ List.range 8,CorrectAt 12 (112+i):=by decide +kernel

theorem cr12p15:∀ i ∈ List.range 8,CorrectAt 12 (120+i):=by decide +kernel

theorem cr12p16:∀ i ∈ List.range 3,CorrectAt 12 (128+i):=by decide +kernel

theorem sr12p0:∀ i ∈ List.range 1,StrictCheckAt 12 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 0) 12 0:=by decide +kernel
  have hfast:StrictAtFast (row 12 0) 12 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 0) 12 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 0) 12 0 hvalid hfast

theorem sr12p1:∀ i ∈ List.range 1,StrictCheckAt 12 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 1) 12 1:=by decide +kernel
  have hfast:StrictAtFast (row 12 1) 12 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 1) 12 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 1) 12 1 hvalid hfast

theorem sr12p2:∀ i ∈ List.range 1,StrictCheckAt 12 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 2) 12 2:=by decide +kernel
  have hfast:StrictAtFast (row 12 2) 12 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 2) 12 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 2) 12 2 hvalid hfast

theorem sr12p3:∀ i ∈ List.range 1,StrictCheckAt 12 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 3) 12 3:=by decide +kernel
  have hfast:StrictAtFast (row 12 3) 12 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 3) 12 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 3) 12 3 hvalid hfast

theorem sr12p4:∀ i ∈ List.range 1,StrictCheckAt 12 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 4) 12 4:=by decide +kernel
  have hfast:StrictAtFast (row 12 4) 12 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 4) 12 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 4) 12 4 hvalid hfast

theorem sr12p5:∀ i ∈ List.range 1,StrictCheckAt 12 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 5) 12 5:=by decide +kernel
  have hfast:StrictAtFast (row 12 5) 12 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 5) 12 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 5) 12 5 hvalid hfast

theorem sr12p6:∀ i ∈ List.range 1,StrictCheckAt 12 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 6) 12 6:=by decide +kernel
  have hfast:StrictAtFast (row 12 6) 12 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 6) 12 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 6) 12 6 hvalid hfast

theorem sr12p7:∀ i ∈ List.range 1,StrictCheckAt 12 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 7) 12 7:=by decide +kernel
  have hfast:StrictAtFast (row 12 7) 12 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 7) 12 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 7) 12 7 hvalid hfast

theorem sr12p8:∀ i ∈ List.range 1,StrictCheckAt 12 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 8) 12 8:=by decide +kernel
  have hfast:StrictAtFast (row 12 8) 12 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 8) 12 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 8) 12 8 hvalid hfast

theorem sr12p9:∀ i ∈ List.range 1,StrictCheckAt 12 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 9) 12 9:=by decide +kernel
  have hfast:StrictAtFast (row 12 9) 12 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 9) 12 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 9) 12 9 hvalid hfast

theorem sr12p10:∀ i ∈ List.range 1,StrictCheckAt 12 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 10) 12 10:=by decide +kernel
  have hfast:StrictAtFast (row 12 10) 12 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 10) 12 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 10) 12 10 hvalid hfast

theorem sr12p11:∀ i ∈ List.range 1,StrictCheckAt 12 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 11) 12 11:=by decide +kernel
  have hfast:StrictAtFast (row 12 11) 12 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 11) 12 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 11) 12 11 hvalid hfast

theorem sr12p12:∀ i ∈ List.range 1,StrictCheckAt 12 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 12) 12 12:=by decide +kernel
  have hfast:StrictAtFast (row 12 12) 12 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 12) 12 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 12) 12 12 hvalid hfast

theorem sr12p13:∀ i ∈ List.range 1,StrictCheckAt 12 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 13) 12 13:=by decide +kernel
  have hfast:StrictAtFast (row 12 13) 12 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 13) 12 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 13) 12 13 hvalid hfast

theorem sr12p14:∀ i ∈ List.range 1,StrictCheckAt 12 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 14) 12 14:=by decide +kernel
  have hfast:StrictAtFast (row 12 14) 12 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 14) 12 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 14) 12 14 hvalid hfast

theorem sr12p15:∀ i ∈ List.range 1,StrictCheckAt 12 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 15) 12 15:=by decide +kernel
  have hfast:StrictAtFast (row 12 15) 12 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 15) 12 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 15) 12 15 hvalid hfast

theorem sr12p16:∀ i ∈ List.range 1,StrictCheckAt 12 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 16) 12 16:=by decide +kernel
  have hfast:StrictAtFast (row 12 16) 12 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 16) 12 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 16) 12 16 hvalid hfast

theorem sr12p17:∀ i ∈ List.range 1,StrictCheckAt 12 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 17) 12 17:=by decide +kernel
  have hfast:StrictAtFast (row 12 17) 12 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 17) 12 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 17) 12 17 hvalid hfast

theorem sr12p18:∀ i ∈ List.range 1,StrictCheckAt 12 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 18) 12 18:=by decide +kernel
  have hfast:StrictAtFast (row 12 18) 12 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 18) 12 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 18) 12 18 hvalid hfast

theorem sr12p19:∀ i ∈ List.range 1,StrictCheckAt 12 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 19) 12 19:=by decide +kernel
  have hfast:StrictAtFast (row 12 19) 12 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 19) 12 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 19) 12 19 hvalid hfast

theorem sr12p20:∀ i ∈ List.range 1,StrictCheckAt 12 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 20) 12 20:=by decide +kernel
  have hfast:StrictAtFast (row 12 20) 12 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 20) 12 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 20) 12 20 hvalid hfast

theorem sr12p21:∀ i ∈ List.range 1,StrictCheckAt 12 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 21) 12 21:=by decide +kernel
  have hfast:StrictAtFast (row 12 21) 12 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 21) 12 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 21) 12 21 hvalid hfast

theorem sr12p22:∀ i ∈ List.range 1,StrictCheckAt 12 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 22) 12 22:=by decide +kernel
  have hfast:StrictAtFast (row 12 22) 12 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 22) 12 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 22) 12 22 hvalid hfast

theorem sr12p23:∀ i ∈ List.range 1,StrictCheckAt 12 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 23) 12 23:=by decide +kernel
  have hfast:StrictAtFast (row 12 23) 12 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 23) 12 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 23) 12 23 hvalid hfast

theorem sr12p24:∀ i ∈ List.range 1,StrictCheckAt 12 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 24) 12 24:=by decide +kernel
  have hfast:StrictAtFast (row 12 24) 12 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 24) 12 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 24) 12 24 hvalid hfast

theorem sr12p25:∀ i ∈ List.range 1,StrictCheckAt 12 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 25) 12 25:=by decide +kernel
  have hfast:StrictAtFast (row 12 25) 12 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 25) 12 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 25) 12 25 hvalid hfast

theorem sr12p26:∀ i ∈ List.range 1,StrictCheckAt 12 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 26) 12 26:=by decide +kernel
  have hfast:StrictAtFast (row 12 26) 12 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 26) 12 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 26) 12 26 hvalid hfast

theorem sr12p27:∀ i ∈ List.range 1,StrictCheckAt 12 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 27) 12 27:=by decide +kernel
  have hfast:StrictAtFast (row 12 27) 12 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 27) 12 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 27) 12 27 hvalid hfast

theorem sr12p28:∀ i ∈ List.range 1,StrictCheckAt 12 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 28) 12 28:=by decide +kernel
  have hfast:StrictAtFast (row 12 28) 12 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 28) 12 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 28) 12 28 hvalid hfast

theorem sr12p29:∀ i ∈ List.range 1,StrictCheckAt 12 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 29) 12 29:=by decide +kernel
  have hfast:StrictAtFast (row 12 29) 12 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 29) 12 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 29) 12 29 hvalid hfast

theorem sr12p30:∀ i ∈ List.range 1,StrictCheckAt 12 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 30) 12 30:=by decide +kernel
  have hfast:StrictAtFast (row 12 30) 12 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 30) 12 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 30) 12 30 hvalid hfast

theorem sr12p31:∀ i ∈ List.range 1,StrictCheckAt 12 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 31) 12 31:=by decide +kernel
  have hfast:StrictAtFast (row 12 31) 12 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 31) 12 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 31) 12 31 hvalid hfast

theorem sr12p32:∀ i ∈ List.range 1,StrictCheckAt 12 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 32) 12 32:=by decide +kernel
  have hfast:StrictAtFast (row 12 32) 12 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 32) 12 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 32) 12 32 hvalid hfast

theorem sr12p33:∀ i ∈ List.range 1,StrictCheckAt 12 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 33) 12 33:=by decide +kernel
  have hfast:StrictAtFast (row 12 33) 12 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 33) 12 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 33) 12 33 hvalid hfast

theorem sr12p34:∀ i ∈ List.range 1,StrictCheckAt 12 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 34) 12 34:=by decide +kernel
  have hfast:StrictAtFast (row 12 34) 12 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 34) 12 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 34) 12 34 hvalid hfast

theorem sr12p35:∀ i ∈ List.range 1,StrictCheckAt 12 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 35) 12 35:=by decide +kernel
  have hfast:StrictAtFast (row 12 35) 12 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 35) 12 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 35) 12 35 hvalid hfast

theorem sr12p36:∀ i ∈ List.range 1,StrictCheckAt 12 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 36) 12 36:=by decide +kernel
  have hfast:StrictAtFast (row 12 36) 12 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 36) 12 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 36) 12 36 hvalid hfast

theorem sr12p37:∀ i ∈ List.range 1,StrictCheckAt 12 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 37) 12 37:=by decide +kernel
  have hfast:StrictAtFast (row 12 37) 12 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 37) 12 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 37) 12 37 hvalid hfast

theorem sr12p38:∀ i ∈ List.range 1,StrictCheckAt 12 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 38) 12 38:=by decide +kernel
  have hfast:StrictAtFast (row 12 38) 12 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 38) 12 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 38) 12 38 hvalid hfast

theorem sr12p39:∀ i ∈ List.range 1,StrictCheckAt 12 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 39) 12 39:=by decide +kernel
  have hfast:StrictAtFast (row 12 39) 12 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 39) 12 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 39) 12 39 hvalid hfast

theorem sr12p40:∀ i ∈ List.range 1,StrictCheckAt 12 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 40) 12 40:=by decide +kernel
  have hfast:StrictAtFast (row 12 40) 12 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 40) 12 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 40) 12 40 hvalid hfast

theorem sr12p41:∀ i ∈ List.range 1,StrictCheckAt 12 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 41) 12 41:=by decide +kernel
  have hfast:StrictAtFast (row 12 41) 12 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 41) 12 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 41) 12 41 hvalid hfast

theorem sr12p42:∀ i ∈ List.range 1,StrictCheckAt 12 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 42) 12 42:=by decide +kernel
  have hfast:StrictAtFast (row 12 42) 12 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 42) 12 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 42) 12 42 hvalid hfast

theorem sr12p43:∀ i ∈ List.range 1,StrictCheckAt 12 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 43) 12 43:=by decide +kernel
  have hfast:StrictAtFast (row 12 43) 12 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 43) 12 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 43) 12 43 hvalid hfast

theorem sr12p44:∀ i ∈ List.range 1,StrictCheckAt 12 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 44) 12 44:=by decide +kernel
  have hfast:StrictAtFast (row 12 44) 12 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 44) 12 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 44) 12 44 hvalid hfast

theorem sr12p45:∀ i ∈ List.range 1,StrictCheckAt 12 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 45) 12 45:=by decide +kernel
  have hfast:StrictAtFast (row 12 45) 12 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 45) 12 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 45) 12 45 hvalid hfast

theorem sr12p46:∀ i ∈ List.range 1,StrictCheckAt 12 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 46) 12 46:=by decide +kernel
  have hfast:StrictAtFast (row 12 46) 12 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 46) 12 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 46) 12 46 hvalid hfast

theorem sr12p47:∀ i ∈ List.range 1,StrictCheckAt 12 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 47) 12 47:=by decide +kernel
  have hfast:StrictAtFast (row 12 47) 12 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 47) 12 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 47) 12 47 hvalid hfast

theorem sr12p48:∀ i ∈ List.range 1,StrictCheckAt 12 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 48) 12 48:=by decide +kernel
  have hfast:StrictAtFast (row 12 48) 12 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 48) 12 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 48) 12 48 hvalid hfast

theorem sr12p49:∀ i ∈ List.range 1,StrictCheckAt 12 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 49) 12 49:=by decide +kernel
  have hfast:StrictAtFast (row 12 49) 12 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 49) 12 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 49) 12 49 hvalid hfast

theorem sr12p50:∀ i ∈ List.range 1,StrictCheckAt 12 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 50) 12 50:=by decide +kernel
  have hfast:StrictAtFast (row 12 50) 12 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 50) 12 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 50) 12 50 hvalid hfast

theorem sr12p51:∀ i ∈ List.range 1,StrictCheckAt 12 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 51) 12 51:=by decide +kernel
  have hfast:StrictAtFast (row 12 51) 12 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 51) 12 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 51) 12 51 hvalid hfast

theorem sr12p52:∀ i ∈ List.range 1,StrictCheckAt 12 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 52) 12 52:=by decide +kernel
  have hfast:StrictAtFast (row 12 52) 12 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 52) 12 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 52) 12 52 hvalid hfast

theorem sr12p53:∀ i ∈ List.range 1,StrictCheckAt 12 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 53) 12 53:=by decide +kernel
  have hfast:StrictAtFast (row 12 53) 12 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 53) 12 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 53) 12 53 hvalid hfast

theorem sr12p54:∀ i ∈ List.range 1,StrictCheckAt 12 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 54) 12 54:=by decide +kernel
  have hfast:StrictAtFast (row 12 54) 12 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 54) 12 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 54) 12 54 hvalid hfast

theorem sr12p55:∀ i ∈ List.range 1,StrictCheckAt 12 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 55) 12 55:=by decide +kernel
  have hfast:StrictAtFast (row 12 55) 12 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 55) 12 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 55) 12 55 hvalid hfast

theorem sr12p56:∀ i ∈ List.range 1,StrictCheckAt 12 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 56) 12 56:=by decide +kernel
  have hfast:StrictAtFast (row 12 56) 12 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 56) 12 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 56) 12 56 hvalid hfast

theorem sr12p57:∀ i ∈ List.range 1,StrictCheckAt 12 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 57) 12 57:=by decide +kernel
  have hfast:StrictAtFast (row 12 57) 12 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 57) 12 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 57) 12 57 hvalid hfast

theorem sr12p58:∀ i ∈ List.range 1,StrictCheckAt 12 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 58) 12 58:=by decide +kernel
  have hfast:StrictAtFast (row 12 58) 12 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 58) 12 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 58) 12 58 hvalid hfast

theorem sr12p59:∀ i ∈ List.range 1,StrictCheckAt 12 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 59) 12 59:=by decide +kernel
  have hfast:StrictAtFast (row 12 59) 12 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 59) 12 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 59) 12 59 hvalid hfast

theorem sr12p60:∀ i ∈ List.range 1,StrictCheckAt 12 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 60) 12 60:=by decide +kernel
  have hfast:StrictAtFast (row 12 60) 12 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 60) 12 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 60) 12 60 hvalid hfast

theorem sr12p61:∀ i ∈ List.range 1,StrictCheckAt 12 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 61) 12 61:=by decide +kernel
  have hfast:StrictAtFast (row 12 61) 12 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 61) 12 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 61) 12 61 hvalid hfast

theorem sr12p62:∀ i ∈ List.range 1,StrictCheckAt 12 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 62) 12 62:=by decide +kernel
  have hfast:StrictAtFast (row 12 62) 12 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 62) 12 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 62) 12 62 hvalid hfast

theorem sr12p63:∀ i ∈ List.range 1,StrictCheckAt 12 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 63) 12 63:=by decide +kernel
  have hfast:StrictAtFast (row 12 63) 12 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 63) 12 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 63) 12 63 hvalid hfast

theorem sr12p64:∀ i ∈ List.range 1,StrictCheckAt 12 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 64) 12 64:=by decide +kernel
  have hfast:StrictAtFast (row 12 64) 12 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 64) 12 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 64) 12 64 hvalid hfast

theorem sr12p65:∀ i ∈ List.range 1,StrictCheckAt 12 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 65) 12 65:=by decide +kernel
  have hfast:StrictAtFast (row 12 65) 12 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 65) 12 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 65) 12 65 hvalid hfast

theorem sr12p66:∀ i ∈ List.range 1,StrictCheckAt 12 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 66) 12 66:=by decide +kernel
  have hfast:StrictAtFast (row 12 66) 12 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 66) 12 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 66) 12 66 hvalid hfast

theorem sr12p67:∀ i ∈ List.range 1,StrictCheckAt 12 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 67) 12 67:=by decide +kernel
  have hfast:StrictAtFast (row 12 67) 12 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 67) 12 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 67) 12 67 hvalid hfast

theorem sr12p68:∀ i ∈ List.range 1,StrictCheckAt 12 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 68) 12 68:=by decide +kernel
  have hfast:StrictAtFast (row 12 68) 12 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 68) 12 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 68) 12 68 hvalid hfast

theorem sr12p69:∀ i ∈ List.range 1,StrictCheckAt 12 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 69) 12 69:=by decide +kernel
  have hfast:StrictAtFast (row 12 69) 12 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 69) 12 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 69) 12 69 hvalid hfast

theorem sr12p70:∀ i ∈ List.range 1,StrictCheckAt 12 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 70) 12 70:=by decide +kernel
  have hfast:StrictAtFast (row 12 70) 12 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 70) 12 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 70) 12 70 hvalid hfast

theorem sr12p71:∀ i ∈ List.range 1,StrictCheckAt 12 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 71) 12 71:=by decide +kernel
  have hfast:StrictAtFast (row 12 71) 12 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 71) 12 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 71) 12 71 hvalid hfast

theorem sr12p72:∀ i ∈ List.range 1,StrictCheckAt 12 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 72) 12 72:=by decide +kernel
  have hfast:StrictAtFast (row 12 72) 12 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 72) 12 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 72) 12 72 hvalid hfast

theorem sr12p73:∀ i ∈ List.range 1,StrictCheckAt 12 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 73) 12 73:=by decide +kernel
  have hfast:StrictAtFast (row 12 73) 12 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 73) 12 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 73) 12 73 hvalid hfast

theorem sr12p74:∀ i ∈ List.range 1,StrictCheckAt 12 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 74) 12 74:=by decide +kernel
  have hfast:StrictAtFast (row 12 74) 12 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 74) 12 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 74) 12 74 hvalid hfast

theorem sr12p75:∀ i ∈ List.range 1,StrictCheckAt 12 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 75) 12 75:=by decide +kernel
  have hfast:StrictAtFast (row 12 75) 12 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 75) 12 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 75) 12 75 hvalid hfast

theorem sr12p76:∀ i ∈ List.range 1,StrictCheckAt 12 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 76) 12 76:=by decide +kernel
  have hfast:StrictAtFast (row 12 76) 12 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 76) 12 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 76) 12 76 hvalid hfast

theorem sr12p77:∀ i ∈ List.range 1,StrictCheckAt 12 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 77) 12 77:=by decide +kernel
  have hfast:StrictAtFast (row 12 77) 12 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 77) 12 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 77) 12 77 hvalid hfast

theorem sr12p78:∀ i ∈ List.range 1,StrictCheckAt 12 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 78) 12 78:=by decide +kernel
  have hfast:StrictAtFast (row 12 78) 12 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 78) 12 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 78) 12 78 hvalid hfast

theorem sr12p79:∀ i ∈ List.range 1,StrictCheckAt 12 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 79) 12 79:=by decide +kernel
  have hfast:StrictAtFast (row 12 79) 12 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 79) 12 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 79) 12 79 hvalid hfast

theorem sr12p80:∀ i ∈ List.range 1,StrictCheckAt 12 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 80) 12 80:=by decide +kernel
  have hfast:StrictAtFast (row 12 80) 12 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 80) 12 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 80) 12 80 hvalid hfast

theorem sr12p81:∀ i ∈ List.range 1,StrictCheckAt 12 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 81) 12 81:=by decide +kernel
  have hfast:StrictAtFast (row 12 81) 12 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 81) 12 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 81) 12 81 hvalid hfast

theorem sr12p82:∀ i ∈ List.range 1,StrictCheckAt 12 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 82) 12 82:=by decide +kernel
  have hfast:StrictAtFast (row 12 82) 12 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 82) 12 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 82) 12 82 hvalid hfast

theorem sr12p83:∀ i ∈ List.range 1,StrictCheckAt 12 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 83) 12 83:=by decide +kernel
  have hfast:StrictAtFast (row 12 83) 12 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 83) 12 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 83) 12 83 hvalid hfast

theorem sr12p84:∀ i ∈ List.range 1,StrictCheckAt 12 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 84) 12 84:=by decide +kernel
  have hfast:StrictAtFast (row 12 84) 12 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 84) 12 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 84) 12 84 hvalid hfast

theorem sr12p85:∀ i ∈ List.range 1,StrictCheckAt 12 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 85) 12 85:=by decide +kernel
  have hfast:StrictAtFast (row 12 85) 12 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 85) 12 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 85) 12 85 hvalid hfast

theorem sr12p86:∀ i ∈ List.range 1,StrictCheckAt 12 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 86) 12 86:=by decide +kernel
  have hfast:StrictAtFast (row 12 86) 12 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 86) 12 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 86) 12 86 hvalid hfast

theorem sr12p87:∀ i ∈ List.range 1,StrictCheckAt 12 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 87) 12 87:=by decide +kernel
  have hfast:StrictAtFast (row 12 87) 12 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 87) 12 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 87) 12 87 hvalid hfast

theorem sr12p88:∀ i ∈ List.range 1,StrictCheckAt 12 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 88) 12 88:=by decide +kernel
  have hfast:StrictAtFast (row 12 88) 12 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 88) 12 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 88) 12 88 hvalid hfast

theorem sr12p89:∀ i ∈ List.range 1,StrictCheckAt 12 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 89) 12 89:=by decide +kernel
  have hfast:StrictAtFast (row 12 89) 12 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 89) 12 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 89) 12 89 hvalid hfast

theorem sr12p90:∀ i ∈ List.range 1,StrictCheckAt 12 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 90) 12 90:=by decide +kernel
  have hfast:StrictAtFast (row 12 90) 12 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 90) 12 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 90) 12 90 hvalid hfast

theorem sr12p91:∀ i ∈ List.range 1,StrictCheckAt 12 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 91) 12 91:=by decide +kernel
  have hfast:StrictAtFast (row 12 91) 12 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 91) 12 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 91) 12 91 hvalid hfast

theorem sr12p92:∀ i ∈ List.range 1,StrictCheckAt 12 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 92) 12 92:=by decide +kernel
  have hfast:StrictAtFast (row 12 92) 12 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 92) 12 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 92) 12 92 hvalid hfast

theorem sr12p93:∀ i ∈ List.range 1,StrictCheckAt 12 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 93) 12 93:=by decide +kernel
  have hfast:StrictAtFast (row 12 93) 12 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 93) 12 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 93) 12 93 hvalid hfast

theorem sr12p94:∀ i ∈ List.range 1,StrictCheckAt 12 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 94) 12 94:=by decide +kernel
  have hfast:StrictAtFast (row 12 94) 12 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 94) 12 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 94) 12 94 hvalid hfast

theorem sr12p95:∀ i ∈ List.range 1,StrictCheckAt 12 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 95) 12 95:=by decide +kernel
  have hfast:StrictAtFast (row 12 95) 12 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 95) 12 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 95) 12 95 hvalid hfast

theorem sr12p96:∀ i ∈ List.range 1,StrictCheckAt 12 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 96) 12 96:=by decide +kernel
  have hfast:StrictAtFast (row 12 96) 12 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 96) 12 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 96) 12 96 hvalid hfast

theorem sr12p97:∀ i ∈ List.range 1,StrictCheckAt 12 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 97) 12 97:=by decide +kernel
  have hfast:StrictAtFast (row 12 97) 12 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 97) 12 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 97) 12 97 hvalid hfast

theorem sr12p98:∀ i ∈ List.range 1,StrictCheckAt 12 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 98) 12 98:=by decide +kernel
  have hfast:StrictAtFast (row 12 98) 12 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 98) 12 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 98) 12 98 hvalid hfast

theorem sr12p99:∀ i ∈ List.range 1,StrictCheckAt 12 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 99) 12 99:=by decide +kernel
  have hfast:StrictAtFast (row 12 99) 12 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 99) 12 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 99) 12 99 hvalid hfast

theorem sr12p100:∀ i ∈ List.range 1,StrictCheckAt 12 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 100) 12 100:=by decide +kernel
  have hfast:StrictAtFast (row 12 100) 12 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 100) 12 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 100) 12 100 hvalid hfast

theorem sr12p101:∀ i ∈ List.range 1,StrictCheckAt 12 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 101) 12 101:=by decide +kernel
  have hfast:StrictAtFast (row 12 101) 12 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 101) 12 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 101) 12 101 hvalid hfast

theorem sr12p102:∀ i ∈ List.range 1,StrictCheckAt 12 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 102) 12 102:=by decide +kernel
  have hfast:StrictAtFast (row 12 102) 12 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 102) 12 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 102) 12 102 hvalid hfast

theorem sr12p103:∀ i ∈ List.range 1,StrictCheckAt 12 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 103) 12 103:=by decide +kernel
  have hfast:StrictAtFast (row 12 103) 12 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 103) 12 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 103) 12 103 hvalid hfast

theorem sr12p104:∀ i ∈ List.range 1,StrictCheckAt 12 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 104) 12 104:=by decide +kernel
  have hfast:StrictAtFast (row 12 104) 12 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 104) 12 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 104) 12 104 hvalid hfast

theorem sr12p105:∀ i ∈ List.range 1,StrictCheckAt 12 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 105) 12 105:=by decide +kernel
  have hfast:StrictAtFast (row 12 105) 12 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 105) 12 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 105) 12 105 hvalid hfast

theorem sr12p106:∀ i ∈ List.range 1,StrictCheckAt 12 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 106) 12 106:=by decide +kernel
  have hfast:StrictAtFast (row 12 106) 12 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 106) 12 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 106) 12 106 hvalid hfast

theorem sr12p107:∀ i ∈ List.range 1,StrictCheckAt 12 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 107) 12 107:=by decide +kernel
  have hfast:StrictAtFast (row 12 107) 12 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 107) 12 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 107) 12 107 hvalid hfast

theorem sr12p108:∀ i ∈ List.range 1,StrictCheckAt 12 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 108) 12 108:=by decide +kernel
  have hfast:StrictAtFast (row 12 108) 12 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 108) 12 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 108) 12 108 hvalid hfast

theorem sr12p109:∀ i ∈ List.range 1,StrictCheckAt 12 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 109) 12 109:=by decide +kernel
  have hfast:StrictAtFast (row 12 109) 12 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 109) 12 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 109) 12 109 hvalid hfast

theorem sr12p110:∀ i ∈ List.range 1,StrictCheckAt 12 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 110) 12 110:=by decide +kernel
  have hfast:StrictAtFast (row 12 110) 12 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 110) 12 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 110) 12 110 hvalid hfast

theorem sr12p111:∀ i ∈ List.range 1,StrictCheckAt 12 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 111) 12 111:=by decide +kernel
  have hfast:StrictAtFast (row 12 111) 12 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 111) 12 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 111) 12 111 hvalid hfast

theorem sr12p112:∀ i ∈ List.range 1,StrictCheckAt 12 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 112) 12 112:=by decide +kernel
  have hfast:StrictAtFast (row 12 112) 12 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 112) 12 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 112) 12 112 hvalid hfast

theorem sr12p113:∀ i ∈ List.range 1,StrictCheckAt 12 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 113) 12 113:=by decide +kernel
  have hfast:StrictAtFast (row 12 113) 12 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 113) 12 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 113) 12 113 hvalid hfast

theorem sr12p114:∀ i ∈ List.range 1,StrictCheckAt 12 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 114) 12 114:=by decide +kernel
  have hfast:StrictAtFast (row 12 114) 12 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 114) 12 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 114) 12 114 hvalid hfast

theorem sr12p115:∀ i ∈ List.range 1,StrictCheckAt 12 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 115) 12 115:=by decide +kernel
  have hfast:StrictAtFast (row 12 115) 12 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 115) 12 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 115) 12 115 hvalid hfast

theorem sr12p116:∀ i ∈ List.range 1,StrictCheckAt 12 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 116) 12 116:=by decide +kernel
  have hfast:StrictAtFast (row 12 116) 12 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 116) 12 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 116) 12 116 hvalid hfast

theorem sr12p117:∀ i ∈ List.range 1,StrictCheckAt 12 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 117) 12 117:=by decide +kernel
  have hfast:StrictAtFast (row 12 117) 12 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 117) 12 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 117) 12 117 hvalid hfast

theorem sr12p118:∀ i ∈ List.range 1,StrictCheckAt 12 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 118) 12 118:=by decide +kernel
  have hfast:StrictAtFast (row 12 118) 12 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 118) 12 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 118) 12 118 hvalid hfast

theorem sr12p119:∀ i ∈ List.range 1,StrictCheckAt 12 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 119) 12 119:=by decide +kernel
  have hfast:StrictAtFast (row 12 119) 12 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 119) 12 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 119) 12 119 hvalid hfast

theorem sr12p120:∀ i ∈ List.range 1,StrictCheckAt 12 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 120) 12 120:=by decide +kernel
  have hfast:StrictAtFast (row 12 120) 12 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 120) 12 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 120) 12 120 hvalid hfast

theorem sr12p121:∀ i ∈ List.range 1,StrictCheckAt 12 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 121) 12 121:=by decide +kernel
  have hfast:StrictAtFast (row 12 121) 12 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 121) 12 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 121) 12 121 hvalid hfast

theorem sr12p122:∀ i ∈ List.range 1,StrictCheckAt 12 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 122) 12 122:=by decide +kernel
  have hfast:StrictAtFast (row 12 122) 12 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 122) 12 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 122) 12 122 hvalid hfast

theorem sr12p123:∀ i ∈ List.range 1,StrictCheckAt 12 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 123) 12 123:=by decide +kernel
  have hfast:StrictAtFast (row 12 123) 12 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 123) 12 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 123) 12 123 hvalid hfast

theorem sr12p124:∀ i ∈ List.range 1,StrictCheckAt 12 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 124) 12 124:=by decide +kernel
  have hfast:StrictAtFast (row 12 124) 12 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 124) 12 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 124) 12 124 hvalid hfast

theorem sr12p125:∀ i ∈ List.range 1,StrictCheckAt 12 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 125) 12 125:=by decide +kernel
  have hfast:StrictAtFast (row 12 125) 12 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 125) 12 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 125) 12 125 hvalid hfast

theorem sr12p126:∀ i ∈ List.range 1,StrictCheckAt 12 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 126) 12 126:=by decide +kernel
  have hfast:StrictAtFast (row 12 126) 12 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 126) 12 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 126) 12 126 hvalid hfast

theorem sr12p127:∀ i ∈ List.range 1,StrictCheckAt 12 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 127) 12 127:=by decide +kernel
  have hfast:StrictAtFast (row 12 127) 12 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 127) 12 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 127) 12 127 hvalid hfast

theorem sr12p128:∀ i ∈ List.range 1,StrictCheckAt 12 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 128) 12 128:=by decide +kernel
  have hfast:StrictAtFast (row 12 128) 12 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 128) 12 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 128) 12 128 hvalid hfast

theorem sr12p129:∀ i ∈ List.range 1,StrictCheckAt 12 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 129) 12 129:=by decide +kernel
  have hfast:StrictAtFast (row 12 129) 12 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 129) 12 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 129) 12 129 hvalid hfast

theorem sr12p130:∀ i ∈ List.range 1,StrictCheckAt 12 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 130) 12 130:=by decide +kernel
  have hfast:StrictAtFast (row 12 130) 12 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 130) 12 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 130) 12 130 hvalid hfast

theorem br12p0:∀ i ∈ List.range 4,BaseCheckAt 12 (0+i):=by decide +kernel

theorem br12p1:∀ i ∈ List.range 4,BaseCheckAt 12 (4+i):=by decide +kernel

theorem br12p2:∀ i ∈ List.range 4,BaseCheckAt 12 (8+i):=by decide +kernel

theorem br12p3:∀ i ∈ List.range 4,BaseCheckAt 12 (12+i):=by decide +kernel

theorem br12p4:∀ i ∈ List.range 4,BaseCheckAt 12 (16+i):=by decide +kernel

theorem br12p5:∀ i ∈ List.range 4,BaseCheckAt 12 (20+i):=by decide +kernel

theorem br12p6:∀ i ∈ List.range 4,BaseCheckAt 12 (24+i):=by decide +kernel

theorem br12p7:∀ i ∈ List.range 4,BaseCheckAt 12 (28+i):=by decide +kernel

theorem br12p8:∀ i ∈ List.range 4,BaseCheckAt 12 (32+i):=by decide +kernel

theorem br12p9:∀ i ∈ List.range 4,BaseCheckAt 12 (36+i):=by decide +kernel

theorem br12p10:∀ i ∈ List.range 4,BaseCheckAt 12 (40+i):=by decide +kernel

theorem br12p11:∀ i ∈ List.range 4,BaseCheckAt 12 (44+i):=by decide +kernel

theorem br12p12:∀ i ∈ List.range 4,BaseCheckAt 12 (48+i):=by decide +kernel

theorem br12p13:∀ i ∈ List.range 4,BaseCheckAt 12 (52+i):=by decide +kernel

theorem br12p14:∀ i ∈ List.range 4,BaseCheckAt 12 (56+i):=by decide +kernel

theorem br12p15:∀ i ∈ List.range 4,BaseCheckAt 12 (60+i):=by decide +kernel



theorem br12p16:∀ i ∈ List.range 4,BaseCheckAt 12 (64+i):=by decide +kernel

theorem br12p17:∀ i ∈ List.range 4,BaseCheckAt 12 (68+i):=by decide +kernel

theorem br12p18:∀ i ∈ List.range 4,BaseCheckAt 12 (72+i):=by decide +kernel

theorem br12p19:∀ i ∈ List.range 4,BaseCheckAt 12 (76+i):=by decide +kernel

theorem br12p20:∀ i ∈ List.range 4,BaseCheckAt 12 (80+i):=by decide +kernel

theorem br12p21:∀ i ∈ List.range 4,BaseCheckAt 12 (84+i):=by decide +kernel

theorem br12p22:∀ i ∈ List.range 4,BaseCheckAt 12 (88+i):=by decide +kernel

theorem br12p23:∀ i ∈ List.range 4,BaseCheckAt 12 (92+i):=by decide +kernel

theorem br12p24:∀ i ∈ List.range 4,BaseCheckAt 12 (96+i):=by decide +kernel

theorem br12p25:∀ i ∈ List.range 4,BaseCheckAt 12 (100+i):=by decide +kernel

theorem br12p26:∀ i ∈ List.range 4,BaseCheckAt 12 (104+i):=by decide +kernel

theorem br12p27:∀ i ∈ List.range 4,BaseCheckAt 12 (108+i):=by decide +kernel

theorem br12p28:∀ i ∈ List.range 4,BaseCheckAt 12 (112+i):=by decide +kernel

theorem br12p29:∀ i ∈ List.range 4,BaseCheckAt 12 (116+i):=by decide +kernel

theorem br12p30:∀ i ∈ List.range 4,BaseCheckAt 12 (120+i):=by decide +kernel

theorem br12p31:∀ i ∈ List.range 4,BaseCheckAt 12 (124+i):=by decide +kernel



theorem br12p32:∀ i ∈ List.range 3,BaseCheckAt 12 (128+i):=by decide +kernel



theorem cr12:∀ V ∈ List.range 131,CorrectAt 12 V:=by
  intro V hV
  have hv:V < 131:=List.mem_range.mp hV
  by_cases h0_17:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr12p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr12p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr12p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr12p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr12p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr12p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr12p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr12p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_17:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr12p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr12p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr12p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr12p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_17:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr12p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr12p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_17:V < 120
        · have h:=cr12p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h15_17:V < 128
          · have h:=cr12p15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=cr12p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem zr12:∀ V ∈ List.range 131,ZeroCheckAt 12 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 12 V (by omega) (by omega) (by omega)
theorem sr12:∀ V ∈ List.range 131,StrictCheckAt 12 V:=by
  intro V hV
  have hv:V < 131:=List.mem_range.mp hV
  by_cases h0_131:V < 65
  · by_cases h0_65:V < 32
    · by_cases h0_32:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have h:=sr12p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
              · have h:=sr12p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
            · by_cases h2_4:V < 3
              · have h:=sr12p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
              · have h:=sr12p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have h:=sr12p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
              · have h:=sr12p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
            · by_cases h6_8:V < 7
              · have h:=sr12p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
              · have h:=sr12p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have h:=sr12p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr12p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
            · by_cases h10_12:V < 11
              · have h:=sr12p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr12p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have h:=sr12p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr12p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
            · by_cases h14_16:V < 15
              · have h:=sr12p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
              · have h:=sr12p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
      · by_cases h16_32:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have h:=sr12p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr12p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
            · by_cases h18_20:V < 19
              · have h:=sr12p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr12p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have h:=sr12p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr12p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr12p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr12p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
        · by_cases h24_32:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr12p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr12p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr12p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr12p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
          · by_cases h28_32:V < 30
            · by_cases h28_30:V < 29
              · have h:=sr12p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr12p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_32:V < 31
              · have h:=sr12p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · have h:=sr12p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
    · by_cases h32_65:V < 48
      · by_cases h32_48:V < 40
        · by_cases h32_40:V < 36
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have h:=sr12p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr12p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
            · by_cases h34_36:V < 35
              · have h:=sr12p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr12p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have h:=sr12p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr12p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
            · by_cases h38_40:V < 39
              · have h:=sr12p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr12p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
        · by_cases h40_48:V < 44
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have h:=sr12p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr12p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
            · by_cases h42_44:V < 43
              · have h:=sr12p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr12p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have h:=sr12p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr12p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
            · by_cases h46_48:V < 47
              · have h:=sr12p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr12p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
      · by_cases h48_65:V < 56
        · by_cases h48_56:V < 52
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have h:=sr12p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr12p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
            · by_cases h50_52:V < 51
              · have h:=sr12p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr12p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have h:=sr12p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr12p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
            · by_cases h54_56:V < 55
              · have h:=sr12p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr12p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
        · by_cases h56_65:V < 60
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have h:=sr12p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr12p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
            · by_cases h58_60:V < 59
              · have h:=sr12p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr12p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
          · by_cases h60_65:V < 62
            · by_cases h60_62:V < 61
              · have h:=sr12p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr12p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
            · by_cases h62_65:V < 63
              · have h:=sr12p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · by_cases h63_65:V < 64
                · have h:=sr12p63 (V-63) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
                · have h:=sr12p64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
  · by_cases h65_131:V < 98
    · by_cases h65_98:V < 81
      · by_cases h65_81:V < 73
        · by_cases h65_73:V < 69
          · by_cases h65_69:V < 67
            · by_cases h65_67:V < 66
              · have h:=sr12p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr12p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
            · by_cases h67_69:V < 68
              · have h:=sr12p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr12p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have h:=sr12p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr12p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
            · by_cases h71_73:V < 72
              · have h:=sr12p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr12p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h73_81:V < 77
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have h:=sr12p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr12p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
            · by_cases h75_77:V < 76
              · have h:=sr12p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr12p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have h:=sr12p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr12p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
            · by_cases h79_81:V < 80
              · have h:=sr12p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr12p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
      · by_cases h81_98:V < 89
        · by_cases h81_89:V < 85
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have h:=sr12p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr12p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
            · by_cases h83_85:V < 84
              · have h:=sr12p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr12p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have h:=sr12p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr12p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
            · by_cases h87_89:V < 88
              · have h:=sr12p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr12p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h89_98:V < 93
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have h:=sr12p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr12p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr12p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr12p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · by_cases h93_98:V < 95
            · by_cases h93_95:V < 94
              · have h:=sr12p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr12p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
            · by_cases h95_98:V < 96
              · have h:=sr12p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · by_cases h96_98:V < 97
                · have h:=sr12p96 (V-96) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
                · have h:=sr12p97 (V-97) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
    · by_cases h98_131:V < 114
      · by_cases h98_114:V < 106
        · by_cases h98_106:V < 102
          · by_cases h98_102:V < 100
            · by_cases h98_100:V < 99
              · have h:=sr12p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr12p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
            · by_cases h100_102:V < 101
              · have h:=sr12p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr12p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have h:=sr12p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr12p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
            · by_cases h104_106:V < 105
              · have h:=sr12p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr12p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
        · by_cases h106_114:V < 110
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have h:=sr12p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr12p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
            · by_cases h108_110:V < 109
              · have h:=sr12p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr12p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have h:=sr12p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr12p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
            · by_cases h112_114:V < 113
              · have h:=sr12p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr12p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
      · by_cases h114_131:V < 122
        · by_cases h114_122:V < 118
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have h:=sr12p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr12p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
            · by_cases h116_118:V < 117
              · have h:=sr12p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr12p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
          · by_cases h118_122:V < 120
            · by_cases h118_120:V < 119
              · have h:=sr12p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr12p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
            · by_cases h120_122:V < 121
              · have h:=sr12p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
              · have h:=sr12p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
        · by_cases h122_131:V < 126
          · by_cases h122_126:V < 124
            · by_cases h122_124:V < 123
              · have h:=sr12p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
              · have h:=sr12p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
            · by_cases h124_126:V < 125
              · have h:=sr12p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
              · have h:=sr12p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
          · by_cases h126_131:V < 128
            · by_cases h126_128:V < 127
              · have h:=sr12p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h
              · have h:=sr12p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using h
            · by_cases h128_131:V < 129
              · have h:=sr12p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
              · by_cases h129_131:V < 130
                · have h:=sr12p129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using h
                · have h:=sr12p130 (V-130) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using h

theorem br12:∀ V ∈ List.range 131,BaseCheckAt 12 V:=by
  intro V hV
  have hv:V < 131:=List.mem_range.mp hV
  by_cases h0_33:V < 64
  · by_cases h0_16:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br12p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br12p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br12p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br12p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br12p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br12p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br12p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br12p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_16:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br12p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br12p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br12p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br12p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_16:V < 56
        · by_cases h12_14:V < 52
          · have h:=br12p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br12p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_16:V < 60
          · have h:=br12p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · have h:=br12p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h16_33:V < 96
    · by_cases h16_24:V < 80
      · by_cases h16_20:V < 72
        · by_cases h16_18:V < 68
          · have h:=br12p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br12p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h18_20:V < 76
          · have h:=br12p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br12p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h20_24:V < 88
        · by_cases h20_22:V < 84
          · have h:=br12p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br12p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br12p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br12p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h24_33:V < 112
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br12p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br12p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br12p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br12p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h28_33:V < 120
        · by_cases h28_30:V < 116
          · have h:=br12p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br12p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h30_33:V < 124
          · have h:=br12p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · by_cases h31_33:V < 128
            · have h:=br12p31 (V-124) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
            · have h:=br12p32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
