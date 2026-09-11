import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr22p0:∀ i ∈ List.range 8,CorrectAt 22 (0+i):=by decide +kernel

theorem cr22p1:∀ i ∈ List.range 8,CorrectAt 22 (8+i):=by decide +kernel

theorem cr22p2:∀ i ∈ List.range 8,CorrectAt 22 (16+i):=by decide +kernel

theorem cr22p3:∀ i ∈ List.range 8,CorrectAt 22 (24+i):=by decide +kernel

theorem cr22p4:∀ i ∈ List.range 8,CorrectAt 22 (32+i):=by decide +kernel

theorem cr22p5:∀ i ∈ List.range 8,CorrectAt 22 (40+i):=by decide +kernel

theorem cr22p6:∀ i ∈ List.range 8,CorrectAt 22 (48+i):=by decide +kernel

theorem cr22p7:∀ i ∈ List.range 8,CorrectAt 22 (56+i):=by decide +kernel

theorem cr22p8:∀ i ∈ List.range 8,CorrectAt 22 (64+i):=by decide +kernel

theorem cr22p9:∀ i ∈ List.range 8,CorrectAt 22 (72+i):=by decide +kernel

theorem cr22p10:∀ i ∈ List.range 8,CorrectAt 22 (80+i):=by decide +kernel

theorem cr22p11:∀ i ∈ List.range 8,CorrectAt 22 (88+i):=by decide +kernel

theorem cr22p12:∀ i ∈ List.range 8,CorrectAt 22 (96+i):=by decide +kernel

theorem cr22p13:∀ i ∈ List.range 8,CorrectAt 22 (104+i):=by decide +kernel

theorem cr22p14:∀ i ∈ List.range 8,CorrectAt 22 (112+i):=by decide +kernel

theorem cr22p15:∀ i ∈ List.range 1,CorrectAt 22 (120+i):=by decide +kernel

theorem sr22p0:∀ i ∈ List.range 1,StrictCheckAt 22 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 0) 22 0:=by decide +kernel
  have hfast:StrictAtFast (row 22 0) 22 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 0) 22 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 0) 22 0 hvalid hfast

theorem sr22p1:∀ i ∈ List.range 1,StrictCheckAt 22 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 1) 22 1:=by decide +kernel
  have hfast:StrictAtFast (row 22 1) 22 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 1) 22 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 1) 22 1 hvalid hfast

theorem sr22p2:∀ i ∈ List.range 1,StrictCheckAt 22 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 2) 22 2:=by decide +kernel
  have hfast:StrictAtFast (row 22 2) 22 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 2) 22 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 2) 22 2 hvalid hfast

theorem sr22p3:∀ i ∈ List.range 1,StrictCheckAt 22 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 3) 22 3:=by decide +kernel
  have hfast:StrictAtFast (row 22 3) 22 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 3) 22 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 3) 22 3 hvalid hfast

theorem sr22p4:∀ i ∈ List.range 1,StrictCheckAt 22 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 4) 22 4:=by decide +kernel
  have hfast:StrictAtFast (row 22 4) 22 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 4) 22 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 4) 22 4 hvalid hfast

theorem sr22p5:∀ i ∈ List.range 1,StrictCheckAt 22 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 5) 22 5:=by decide +kernel
  have hfast:StrictAtFast (row 22 5) 22 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 5) 22 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 5) 22 5 hvalid hfast

theorem sr22p6:∀ i ∈ List.range 1,StrictCheckAt 22 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 6) 22 6:=by decide +kernel
  have hfast:StrictAtFast (row 22 6) 22 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 6) 22 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 6) 22 6 hvalid hfast

theorem sr22p7:∀ i ∈ List.range 1,StrictCheckAt 22 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 7) 22 7:=by decide +kernel
  have hfast:StrictAtFast (row 22 7) 22 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 7) 22 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 7) 22 7 hvalid hfast

theorem sr22p8:∀ i ∈ List.range 1,StrictCheckAt 22 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 8) 22 8:=by decide +kernel
  have hfast:StrictAtFast (row 22 8) 22 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 8) 22 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 8) 22 8 hvalid hfast

theorem sr22p9:∀ i ∈ List.range 1,StrictCheckAt 22 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 9) 22 9:=by decide +kernel
  have hfast:StrictAtFast (row 22 9) 22 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 9) 22 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 9) 22 9 hvalid hfast

theorem sr22p10:∀ i ∈ List.range 1,StrictCheckAt 22 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 10) 22 10:=by decide +kernel
  have hfast:StrictAtFast (row 22 10) 22 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 10) 22 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 10) 22 10 hvalid hfast

theorem sr22p11:∀ i ∈ List.range 1,StrictCheckAt 22 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 11) 22 11:=by decide +kernel
  have hfast:StrictAtFast (row 22 11) 22 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 11) 22 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 11) 22 11 hvalid hfast

theorem sr22p12:∀ i ∈ List.range 1,StrictCheckAt 22 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 12) 22 12:=by decide +kernel
  have hfast:StrictAtFast (row 22 12) 22 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 12) 22 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 12) 22 12 hvalid hfast

theorem sr22p13:∀ i ∈ List.range 1,StrictCheckAt 22 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 13) 22 13:=by decide +kernel
  have hfast:StrictAtFast (row 22 13) 22 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 13) 22 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 13) 22 13 hvalid hfast

theorem sr22p14:∀ i ∈ List.range 1,StrictCheckAt 22 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 14) 22 14:=by decide +kernel
  have hfast:StrictAtFast (row 22 14) 22 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 14) 22 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 14) 22 14 hvalid hfast

theorem sr22p15:∀ i ∈ List.range 1,StrictCheckAt 22 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 15) 22 15:=by decide +kernel
  have hfast:StrictAtFast (row 22 15) 22 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 15) 22 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 15) 22 15 hvalid hfast

theorem sr22p16:∀ i ∈ List.range 1,StrictCheckAt 22 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 16) 22 16:=by decide +kernel
  have hfast:StrictAtFast (row 22 16) 22 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 16) 22 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 16) 22 16 hvalid hfast

theorem sr22p17:∀ i ∈ List.range 1,StrictCheckAt 22 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 17) 22 17:=by decide +kernel
  have hfast:StrictAtFast (row 22 17) 22 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 17) 22 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 17) 22 17 hvalid hfast

theorem sr22p18:∀ i ∈ List.range 1,StrictCheckAt 22 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 18) 22 18:=by decide +kernel
  have hfast:StrictAtFast (row 22 18) 22 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 18) 22 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 18) 22 18 hvalid hfast

theorem sr22p19:∀ i ∈ List.range 1,StrictCheckAt 22 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 19) 22 19:=by decide +kernel
  have hfast:StrictAtFast (row 22 19) 22 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 19) 22 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 19) 22 19 hvalid hfast

theorem sr22p20:∀ i ∈ List.range 1,StrictCheckAt 22 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 20) 22 20:=by decide +kernel
  have hfast:StrictAtFast (row 22 20) 22 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 20) 22 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 20) 22 20 hvalid hfast

theorem sr22p21:∀ i ∈ List.range 1,StrictCheckAt 22 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 21) 22 21:=by decide +kernel
  have hfast:StrictAtFast (row 22 21) 22 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 21) 22 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 21) 22 21 hvalid hfast

theorem sr22p22:∀ i ∈ List.range 1,StrictCheckAt 22 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 22) 22 22:=by decide +kernel
  have hfast:StrictAtFast (row 22 22) 22 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 22) 22 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 22) 22 22 hvalid hfast

theorem sr22p23:∀ i ∈ List.range 1,StrictCheckAt 22 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 23) 22 23:=by decide +kernel
  have hfast:StrictAtFast (row 22 23) 22 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 23) 22 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 23) 22 23 hvalid hfast

theorem sr22p24:∀ i ∈ List.range 1,StrictCheckAt 22 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 24) 22 24:=by decide +kernel
  have hfast:StrictAtFast (row 22 24) 22 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 24) 22 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 24) 22 24 hvalid hfast

theorem sr22p25:∀ i ∈ List.range 1,StrictCheckAt 22 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 25) 22 25:=by decide +kernel
  have hfast:StrictAtFast (row 22 25) 22 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 25) 22 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 25) 22 25 hvalid hfast

theorem sr22p26:∀ i ∈ List.range 1,StrictCheckAt 22 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 26) 22 26:=by decide +kernel
  have hfast:StrictAtFast (row 22 26) 22 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 26) 22 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 26) 22 26 hvalid hfast

theorem sr22p27:∀ i ∈ List.range 1,StrictCheckAt 22 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 27) 22 27:=by decide +kernel
  have hfast:StrictAtFast (row 22 27) 22 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 27) 22 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 27) 22 27 hvalid hfast

theorem sr22p28:∀ i ∈ List.range 1,StrictCheckAt 22 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 28) 22 28:=by decide +kernel
  have hfast:StrictAtFast (row 22 28) 22 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 28) 22 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 28) 22 28 hvalid hfast

theorem sr22p29:∀ i ∈ List.range 1,StrictCheckAt 22 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 29) 22 29:=by decide +kernel
  have hfast:StrictAtFast (row 22 29) 22 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 29) 22 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 29) 22 29 hvalid hfast

theorem sr22p30:∀ i ∈ List.range 1,StrictCheckAt 22 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 30) 22 30:=by decide +kernel
  have hfast:StrictAtFast (row 22 30) 22 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 30) 22 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 30) 22 30 hvalid hfast

theorem sr22p31:∀ i ∈ List.range 1,StrictCheckAt 22 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 31) 22 31:=by decide +kernel
  have hfast:StrictAtFast (row 22 31) 22 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 31) 22 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 31) 22 31 hvalid hfast

theorem sr22p32:∀ i ∈ List.range 1,StrictCheckAt 22 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 32) 22 32:=by decide +kernel
  have hfast:StrictAtFast (row 22 32) 22 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 32) 22 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 32) 22 32 hvalid hfast

theorem sr22p33:∀ i ∈ List.range 1,StrictCheckAt 22 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 33) 22 33:=by decide +kernel
  have hfast:StrictAtFast (row 22 33) 22 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 33) 22 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 33) 22 33 hvalid hfast

theorem sr22p34:∀ i ∈ List.range 1,StrictCheckAt 22 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 34) 22 34:=by decide +kernel
  have hfast:StrictAtFast (row 22 34) 22 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 34) 22 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 34) 22 34 hvalid hfast

theorem sr22p35:∀ i ∈ List.range 1,StrictCheckAt 22 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 35) 22 35:=by decide +kernel
  have hfast:StrictAtFast (row 22 35) 22 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 35) 22 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 35) 22 35 hvalid hfast

theorem sr22p36:∀ i ∈ List.range 1,StrictCheckAt 22 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 36) 22 36:=by decide +kernel
  have hfast:StrictAtFast (row 22 36) 22 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 36) 22 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 36) 22 36 hvalid hfast

theorem sr22p37:∀ i ∈ List.range 1,StrictCheckAt 22 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 37) 22 37:=by decide +kernel
  have hfast:StrictAtFast (row 22 37) 22 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 37) 22 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 37) 22 37 hvalid hfast

theorem sr22p38:∀ i ∈ List.range 1,StrictCheckAt 22 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 38) 22 38:=by decide +kernel
  have hfast:StrictAtFast (row 22 38) 22 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 38) 22 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 38) 22 38 hvalid hfast

theorem sr22p39:∀ i ∈ List.range 1,StrictCheckAt 22 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 39) 22 39:=by decide +kernel
  have hfast:StrictAtFast (row 22 39) 22 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 39) 22 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 39) 22 39 hvalid hfast

theorem sr22p40:∀ i ∈ List.range 1,StrictCheckAt 22 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 40) 22 40:=by decide +kernel
  have hfast:StrictAtFast (row 22 40) 22 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 40) 22 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 40) 22 40 hvalid hfast

theorem sr22p41:∀ i ∈ List.range 1,StrictCheckAt 22 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 41) 22 41:=by decide +kernel
  have hfast:StrictAtFast (row 22 41) 22 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 41) 22 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 41) 22 41 hvalid hfast

theorem sr22p42:∀ i ∈ List.range 1,StrictCheckAt 22 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 42) 22 42:=by decide +kernel
  have hfast:StrictAtFast (row 22 42) 22 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 42) 22 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 42) 22 42 hvalid hfast

theorem sr22p43:∀ i ∈ List.range 1,StrictCheckAt 22 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 43) 22 43:=by decide +kernel
  have hfast:StrictAtFast (row 22 43) 22 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 43) 22 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 43) 22 43 hvalid hfast

theorem sr22p44:∀ i ∈ List.range 1,StrictCheckAt 22 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 44) 22 44:=by decide +kernel
  have hfast:StrictAtFast (row 22 44) 22 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 44) 22 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 44) 22 44 hvalid hfast

theorem sr22p45:∀ i ∈ List.range 1,StrictCheckAt 22 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 45) 22 45:=by decide +kernel
  have hfast:StrictAtFast (row 22 45) 22 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 45) 22 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 45) 22 45 hvalid hfast

theorem sr22p46:∀ i ∈ List.range 1,StrictCheckAt 22 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 46) 22 46:=by decide +kernel
  have hfast:StrictAtFast (row 22 46) 22 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 46) 22 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 46) 22 46 hvalid hfast

theorem sr22p47:∀ i ∈ List.range 1,StrictCheckAt 22 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 47) 22 47:=by decide +kernel
  have hfast:StrictAtFast (row 22 47) 22 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 47) 22 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 47) 22 47 hvalid hfast

theorem sr22p48:∀ i ∈ List.range 1,StrictCheckAt 22 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 48) 22 48:=by decide +kernel
  have hfast:StrictAtFast (row 22 48) 22 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 48) 22 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 48) 22 48 hvalid hfast

theorem sr22p49:∀ i ∈ List.range 1,StrictCheckAt 22 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 49) 22 49:=by decide +kernel
  have hfast:StrictAtFast (row 22 49) 22 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 49) 22 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 49) 22 49 hvalid hfast

theorem sr22p50:∀ i ∈ List.range 1,StrictCheckAt 22 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 50) 22 50:=by decide +kernel
  have hfast:StrictAtFast (row 22 50) 22 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 50) 22 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 50) 22 50 hvalid hfast

theorem sr22p51:∀ i ∈ List.range 1,StrictCheckAt 22 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 51) 22 51:=by decide +kernel
  have hfast:StrictAtFast (row 22 51) 22 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 51) 22 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 51) 22 51 hvalid hfast

theorem sr22p52:∀ i ∈ List.range 1,StrictCheckAt 22 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 52) 22 52:=by decide +kernel
  have hfast:StrictAtFast (row 22 52) 22 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 52) 22 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 52) 22 52 hvalid hfast

theorem sr22p53:∀ i ∈ List.range 1,StrictCheckAt 22 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 53) 22 53:=by decide +kernel
  have hfast:StrictAtFast (row 22 53) 22 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 53) 22 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 53) 22 53 hvalid hfast

theorem sr22p54:∀ i ∈ List.range 1,StrictCheckAt 22 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 54) 22 54:=by decide +kernel
  have hfast:StrictAtFast (row 22 54) 22 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 54) 22 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 54) 22 54 hvalid hfast

theorem sr22p55:∀ i ∈ List.range 1,StrictCheckAt 22 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 55) 22 55:=by decide +kernel
  have hfast:StrictAtFast (row 22 55) 22 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 55) 22 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 55) 22 55 hvalid hfast

theorem sr22p56:∀ i ∈ List.range 1,StrictCheckAt 22 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 56) 22 56:=by decide +kernel
  have hfast:StrictAtFast (row 22 56) 22 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 56) 22 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 56) 22 56 hvalid hfast

theorem sr22p57:∀ i ∈ List.range 1,StrictCheckAt 22 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 57) 22 57:=by decide +kernel
  have hfast:StrictAtFast (row 22 57) 22 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 57) 22 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 57) 22 57 hvalid hfast

theorem sr22p58:∀ i ∈ List.range 1,StrictCheckAt 22 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 58) 22 58:=by decide +kernel
  have hfast:StrictAtFast (row 22 58) 22 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 58) 22 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 58) 22 58 hvalid hfast

theorem sr22p59:∀ i ∈ List.range 1,StrictCheckAt 22 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 59) 22 59:=by decide +kernel
  have hfast:StrictAtFast (row 22 59) 22 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 59) 22 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 59) 22 59 hvalid hfast

theorem sr22p60:∀ i ∈ List.range 1,StrictCheckAt 22 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 60) 22 60:=by decide +kernel
  have hfast:StrictAtFast (row 22 60) 22 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 60) 22 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 60) 22 60 hvalid hfast

theorem sr22p61:∀ i ∈ List.range 1,StrictCheckAt 22 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 61) 22 61:=by decide +kernel
  have hfast:StrictAtFast (row 22 61) 22 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 61) 22 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 61) 22 61 hvalid hfast

theorem sr22p62:∀ i ∈ List.range 1,StrictCheckAt 22 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 62) 22 62:=by decide +kernel
  have hfast:StrictAtFast (row 22 62) 22 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 62) 22 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 62) 22 62 hvalid hfast

theorem sr22p63:∀ i ∈ List.range 1,StrictCheckAt 22 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 63) 22 63:=by decide +kernel
  have hfast:StrictAtFast (row 22 63) 22 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 63) 22 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 63) 22 63 hvalid hfast

theorem sr22p64:∀ i ∈ List.range 1,StrictCheckAt 22 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 64) 22 64:=by decide +kernel
  have hfast:StrictAtFast (row 22 64) 22 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 64) 22 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 64) 22 64 hvalid hfast

theorem sr22p65:∀ i ∈ List.range 1,StrictCheckAt 22 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 65) 22 65:=by decide +kernel
  have hfast:StrictAtFast (row 22 65) 22 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 65) 22 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 65) 22 65 hvalid hfast

theorem sr22p66:∀ i ∈ List.range 1,StrictCheckAt 22 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 66) 22 66:=by decide +kernel
  have hfast:StrictAtFast (row 22 66) 22 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 66) 22 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 66) 22 66 hvalid hfast

theorem sr22p67:∀ i ∈ List.range 1,StrictCheckAt 22 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 67) 22 67:=by decide +kernel
  have hfast:StrictAtFast (row 22 67) 22 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 67) 22 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 67) 22 67 hvalid hfast

theorem sr22p68:∀ i ∈ List.range 1,StrictCheckAt 22 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 68) 22 68:=by decide +kernel
  have hfast:StrictAtFast (row 22 68) 22 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 68) 22 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 68) 22 68 hvalid hfast

theorem sr22p69:∀ i ∈ List.range 1,StrictCheckAt 22 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 69) 22 69:=by decide +kernel
  have hfast:StrictAtFast (row 22 69) 22 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 69) 22 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 69) 22 69 hvalid hfast

theorem sr22p70:∀ i ∈ List.range 1,StrictCheckAt 22 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 70) 22 70:=by decide +kernel
  have hfast:StrictAtFast (row 22 70) 22 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 70) 22 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 70) 22 70 hvalid hfast

theorem sr22p71:∀ i ∈ List.range 1,StrictCheckAt 22 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 71) 22 71:=by decide +kernel
  have hfast:StrictAtFast (row 22 71) 22 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 71) 22 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 71) 22 71 hvalid hfast

theorem sr22p72:∀ i ∈ List.range 1,StrictCheckAt 22 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 72) 22 72:=by decide +kernel
  have hfast:StrictAtFast (row 22 72) 22 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 72) 22 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 72) 22 72 hvalid hfast

theorem sr22p73:∀ i ∈ List.range 1,StrictCheckAt 22 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 73) 22 73:=by decide +kernel
  have hfast:StrictAtFast (row 22 73) 22 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 73) 22 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 73) 22 73 hvalid hfast

theorem sr22p74:∀ i ∈ List.range 1,StrictCheckAt 22 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 74) 22 74:=by decide +kernel
  have hfast:StrictAtFast (row 22 74) 22 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 74) 22 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 74) 22 74 hvalid hfast

theorem sr22p75:∀ i ∈ List.range 1,StrictCheckAt 22 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 75) 22 75:=by decide +kernel
  have hfast:StrictAtFast (row 22 75) 22 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 75) 22 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 75) 22 75 hvalid hfast

theorem sr22p76:∀ i ∈ List.range 1,StrictCheckAt 22 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 76) 22 76:=by decide +kernel
  have hfast:StrictAtFast (row 22 76) 22 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 76) 22 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 76) 22 76 hvalid hfast

theorem sr22p77:∀ i ∈ List.range 1,StrictCheckAt 22 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 77) 22 77:=by decide +kernel
  have hfast:StrictAtFast (row 22 77) 22 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 77) 22 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 77) 22 77 hvalid hfast

theorem sr22p78:∀ i ∈ List.range 1,StrictCheckAt 22 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 78) 22 78:=by decide +kernel
  have hfast:StrictAtFast (row 22 78) 22 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 78) 22 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 78) 22 78 hvalid hfast

theorem sr22p79:∀ i ∈ List.range 1,StrictCheckAt 22 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 79) 22 79:=by decide +kernel
  have hfast:StrictAtFast (row 22 79) 22 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 79) 22 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 79) 22 79 hvalid hfast

theorem sr22p80:∀ i ∈ List.range 1,StrictCheckAt 22 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 80) 22 80:=by decide +kernel
  have hfast:StrictAtFast (row 22 80) 22 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 80) 22 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 80) 22 80 hvalid hfast

theorem sr22p81:∀ i ∈ List.range 1,StrictCheckAt 22 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 81) 22 81:=by decide +kernel
  have hfast:StrictAtFast (row 22 81) 22 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 81) 22 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 81) 22 81 hvalid hfast

theorem sr22p82:∀ i ∈ List.range 1,StrictCheckAt 22 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 82) 22 82:=by decide +kernel
  have hfast:StrictAtFast (row 22 82) 22 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 82) 22 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 82) 22 82 hvalid hfast

theorem sr22p83:∀ i ∈ List.range 1,StrictCheckAt 22 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 83) 22 83:=by decide +kernel
  have hfast:StrictAtFast (row 22 83) 22 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 83) 22 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 83) 22 83 hvalid hfast

theorem sr22p84:∀ i ∈ List.range 1,StrictCheckAt 22 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 84) 22 84:=by decide +kernel
  have hfast:StrictAtFast (row 22 84) 22 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 84) 22 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 84) 22 84 hvalid hfast

theorem sr22p85:∀ i ∈ List.range 1,StrictCheckAt 22 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 85) 22 85:=by decide +kernel
  have hfast:StrictAtFast (row 22 85) 22 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 85) 22 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 85) 22 85 hvalid hfast

theorem sr22p86:∀ i ∈ List.range 1,StrictCheckAt 22 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 86) 22 86:=by decide +kernel
  have hfast:StrictAtFast (row 22 86) 22 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 86) 22 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 86) 22 86 hvalid hfast

theorem sr22p87:∀ i ∈ List.range 1,StrictCheckAt 22 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 87) 22 87:=by decide +kernel
  have hfast:StrictAtFast (row 22 87) 22 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 87) 22 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 87) 22 87 hvalid hfast

theorem sr22p88:∀ i ∈ List.range 1,StrictCheckAt 22 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 88) 22 88:=by decide +kernel
  have hfast:StrictAtFast (row 22 88) 22 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 88) 22 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 88) 22 88 hvalid hfast

theorem sr22p89:∀ i ∈ List.range 1,StrictCheckAt 22 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 89) 22 89:=by decide +kernel
  have hfast:StrictAtFast (row 22 89) 22 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 89) 22 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 89) 22 89 hvalid hfast

theorem sr22p90:∀ i ∈ List.range 1,StrictCheckAt 22 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 90) 22 90:=by decide +kernel
  have hfast:StrictAtFast (row 22 90) 22 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 90) 22 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 90) 22 90 hvalid hfast

theorem sr22p91:∀ i ∈ List.range 1,StrictCheckAt 22 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 91) 22 91:=by decide +kernel
  have hfast:StrictAtFast (row 22 91) 22 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 91) 22 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 91) 22 91 hvalid hfast

theorem sr22p92:∀ i ∈ List.range 1,StrictCheckAt 22 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 92) 22 92:=by decide +kernel
  have hfast:StrictAtFast (row 22 92) 22 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 92) 22 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 92) 22 92 hvalid hfast

theorem sr22p93:∀ i ∈ List.range 1,StrictCheckAt 22 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 93) 22 93:=by decide +kernel
  have hfast:StrictAtFast (row 22 93) 22 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 93) 22 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 93) 22 93 hvalid hfast

theorem sr22p94:∀ i ∈ List.range 1,StrictCheckAt 22 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 94) 22 94:=by decide +kernel
  have hfast:StrictAtFast (row 22 94) 22 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 94) 22 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 94) 22 94 hvalid hfast

theorem sr22p95:∀ i ∈ List.range 1,StrictCheckAt 22 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 95) 22 95:=by decide +kernel
  have hfast:StrictAtFast (row 22 95) 22 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 95) 22 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 95) 22 95 hvalid hfast

theorem sr22p96:∀ i ∈ List.range 1,StrictCheckAt 22 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 96) 22 96:=by decide +kernel
  have hfast:StrictAtFast (row 22 96) 22 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 96) 22 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 96) 22 96 hvalid hfast

theorem sr22p97:∀ i ∈ List.range 1,StrictCheckAt 22 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 97) 22 97:=by decide +kernel
  have hfast:StrictAtFast (row 22 97) 22 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 97) 22 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 97) 22 97 hvalid hfast

theorem sr22p98:∀ i ∈ List.range 1,StrictCheckAt 22 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 98) 22 98:=by decide +kernel
  have hfast:StrictAtFast (row 22 98) 22 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 98) 22 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 98) 22 98 hvalid hfast

theorem sr22p99:∀ i ∈ List.range 1,StrictCheckAt 22 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 99) 22 99:=by decide +kernel
  have hfast:StrictAtFast (row 22 99) 22 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 99) 22 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 99) 22 99 hvalid hfast

theorem sr22p100:∀ i ∈ List.range 1,StrictCheckAt 22 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 100) 22 100:=by decide +kernel
  have hfast:StrictAtFast (row 22 100) 22 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 100) 22 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 100) 22 100 hvalid hfast

theorem sr22p101:∀ i ∈ List.range 1,StrictCheckAt 22 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 101) 22 101:=by decide +kernel
  have hfast:StrictAtFast (row 22 101) 22 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 101) 22 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 101) 22 101 hvalid hfast

theorem sr22p102:∀ i ∈ List.range 1,StrictCheckAt 22 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 102) 22 102:=by decide +kernel
  have hfast:StrictAtFast (row 22 102) 22 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 102) 22 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 102) 22 102 hvalid hfast

theorem sr22p103:∀ i ∈ List.range 1,StrictCheckAt 22 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 103) 22 103:=by decide +kernel
  have hfast:StrictAtFast (row 22 103) 22 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 103) 22 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 103) 22 103 hvalid hfast

theorem sr22p104:∀ i ∈ List.range 1,StrictCheckAt 22 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 104) 22 104:=by decide +kernel
  have hfast:StrictAtFast (row 22 104) 22 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 104) 22 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 104) 22 104 hvalid hfast

theorem sr22p105:∀ i ∈ List.range 1,StrictCheckAt 22 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 105) 22 105:=by decide +kernel
  have hfast:StrictAtFast (row 22 105) 22 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 105) 22 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 105) 22 105 hvalid hfast

theorem sr22p106:∀ i ∈ List.range 1,StrictCheckAt 22 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 106) 22 106:=by decide +kernel
  have hfast:StrictAtFast (row 22 106) 22 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 106) 22 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 106) 22 106 hvalid hfast

theorem sr22p107:∀ i ∈ List.range 1,StrictCheckAt 22 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 107) 22 107:=by decide +kernel
  have hfast:StrictAtFast (row 22 107) 22 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 107) 22 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 107) 22 107 hvalid hfast

theorem sr22p108:∀ i ∈ List.range 1,StrictCheckAt 22 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 108) 22 108:=by decide +kernel
  have hfast:StrictAtFast (row 22 108) 22 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 108) 22 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 108) 22 108 hvalid hfast

theorem sr22p109:∀ i ∈ List.range 1,StrictCheckAt 22 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 109) 22 109:=by decide +kernel
  have hfast:StrictAtFast (row 22 109) 22 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 109) 22 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 109) 22 109 hvalid hfast

theorem sr22p110:∀ i ∈ List.range 1,StrictCheckAt 22 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 110) 22 110:=by decide +kernel
  have hfast:StrictAtFast (row 22 110) 22 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 110) 22 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 110) 22 110 hvalid hfast

theorem sr22p111:∀ i ∈ List.range 1,StrictCheckAt 22 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 111) 22 111:=by decide +kernel
  have hfast:StrictAtFast (row 22 111) 22 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 111) 22 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 111) 22 111 hvalid hfast

theorem sr22p112:∀ i ∈ List.range 1,StrictCheckAt 22 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 112) 22 112:=by decide +kernel
  have hfast:StrictAtFast (row 22 112) 22 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 112) 22 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 112) 22 112 hvalid hfast

theorem sr22p113:∀ i ∈ List.range 1,StrictCheckAt 22 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 113) 22 113:=by decide +kernel
  have hfast:StrictAtFast (row 22 113) 22 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 113) 22 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 113) 22 113 hvalid hfast

theorem sr22p114:∀ i ∈ List.range 1,StrictCheckAt 22 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 114) 22 114:=by decide +kernel
  have hfast:StrictAtFast (row 22 114) 22 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 114) 22 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 114) 22 114 hvalid hfast

theorem sr22p115:∀ i ∈ List.range 1,StrictCheckAt 22 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 115) 22 115:=by decide +kernel
  have hfast:StrictAtFast (row 22 115) 22 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 115) 22 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 115) 22 115 hvalid hfast

theorem sr22p116:∀ i ∈ List.range 1,StrictCheckAt 22 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 116) 22 116:=by decide +kernel
  have hfast:StrictAtFast (row 22 116) 22 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 116) 22 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 116) 22 116 hvalid hfast

theorem sr22p117:∀ i ∈ List.range 1,StrictCheckAt 22 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 117) 22 117:=by decide +kernel
  have hfast:StrictAtFast (row 22 117) 22 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 117) 22 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 117) 22 117 hvalid hfast

theorem sr22p118:∀ i ∈ List.range 1,StrictCheckAt 22 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 118) 22 118:=by decide +kernel
  have hfast:StrictAtFast (row 22 118) 22 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 118) 22 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 118) 22 118 hvalid hfast

theorem sr22p119:∀ i ∈ List.range 1,StrictCheckAt 22 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 119) 22 119:=by decide +kernel
  have hfast:StrictAtFast (row 22 119) 22 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 119) 22 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 119) 22 119 hvalid hfast

theorem sr22p120:∀ i ∈ List.range 1,StrictCheckAt 22 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 120) 22 120:=by decide +kernel
  have hfast:StrictAtFast (row 22 120) 22 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 120) 22 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 120) 22 120 hvalid hfast

theorem br22p0:∀ i ∈ List.range 4,BaseCheckAt 22 (0+i):=by decide +kernel

theorem br22p1:∀ i ∈ List.range 4,BaseCheckAt 22 (4+i):=by decide +kernel

theorem br22p2:∀ i ∈ List.range 4,BaseCheckAt 22 (8+i):=by decide +kernel

theorem br22p3:∀ i ∈ List.range 4,BaseCheckAt 22 (12+i):=by decide +kernel

theorem br22p4:∀ i ∈ List.range 4,BaseCheckAt 22 (16+i):=by decide +kernel

theorem br22p5:∀ i ∈ List.range 4,BaseCheckAt 22 (20+i):=by decide +kernel

theorem br22p6:∀ i ∈ List.range 4,BaseCheckAt 22 (24+i):=by decide +kernel

theorem br22p7:∀ i ∈ List.range 4,BaseCheckAt 22 (28+i):=by decide +kernel

theorem br22p8:∀ i ∈ List.range 4,BaseCheckAt 22 (32+i):=by decide +kernel

theorem br22p9:∀ i ∈ List.range 4,BaseCheckAt 22 (36+i):=by decide +kernel

theorem br22p10:∀ i ∈ List.range 4,BaseCheckAt 22 (40+i):=by decide +kernel

theorem br22p11:∀ i ∈ List.range 4,BaseCheckAt 22 (44+i):=by decide +kernel

theorem br22p12:∀ i ∈ List.range 4,BaseCheckAt 22 (48+i):=by decide +kernel

theorem br22p13:∀ i ∈ List.range 4,BaseCheckAt 22 (52+i):=by decide +kernel

theorem br22p14:∀ i ∈ List.range 4,BaseCheckAt 22 (56+i):=by decide +kernel

theorem br22p15:∀ i ∈ List.range 4,BaseCheckAt 22 (60+i):=by decide +kernel



theorem br22p16:∀ i ∈ List.range 4,BaseCheckAt 22 (64+i):=by decide +kernel

theorem br22p17:∀ i ∈ List.range 4,BaseCheckAt 22 (68+i):=by decide +kernel

theorem br22p18:∀ i ∈ List.range 4,BaseCheckAt 22 (72+i):=by decide +kernel

theorem br22p19:∀ i ∈ List.range 4,BaseCheckAt 22 (76+i):=by decide +kernel

theorem br22p20:∀ i ∈ List.range 4,BaseCheckAt 22 (80+i):=by decide +kernel

theorem br22p21:∀ i ∈ List.range 4,BaseCheckAt 22 (84+i):=by decide +kernel

theorem br22p22:∀ i ∈ List.range 4,BaseCheckAt 22 (88+i):=by decide +kernel

theorem br22p23:∀ i ∈ List.range 4,BaseCheckAt 22 (92+i):=by decide +kernel

theorem br22p24:∀ i ∈ List.range 4,BaseCheckAt 22 (96+i):=by decide +kernel

theorem br22p25:∀ i ∈ List.range 4,BaseCheckAt 22 (100+i):=by decide +kernel

theorem br22p26:∀ i ∈ List.range 4,BaseCheckAt 22 (104+i):=by decide +kernel

theorem br22p27:∀ i ∈ List.range 4,BaseCheckAt 22 (108+i):=by decide +kernel

theorem br22p28:∀ i ∈ List.range 4,BaseCheckAt 22 (112+i):=by decide +kernel

theorem br22p29:∀ i ∈ List.range 4,BaseCheckAt 22 (116+i):=by decide +kernel

theorem br22p30:∀ i ∈ List.range 1,BaseCheckAt 22 (120+i):=by decide +kernel



theorem cr22:∀ V ∈ List.range 121,CorrectAt 22 V:=by
  intro V hV
  have hv:V < 121:=List.mem_range.mp hV
  by_cases h0_16:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr22p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr22p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr22p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr22p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr22p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr22p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr22p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr22p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_16:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr22p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr22p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr22p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr22p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_16:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr22p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr22p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_16:V < 120
        · have h:=cr22p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · have h:=cr22p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem zr22:∀ V ∈ List.range 121,ZeroCheckAt 22 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 22 V (by omega) (by omega) (by omega)
theorem sr22:∀ V ∈ List.range 121,StrictCheckAt 22 V:=by
  intro V hV
  have hv:V < 121:=List.mem_range.mp hV
  by_cases h0_121:V < 60
  · by_cases h0_60:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr22p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr22p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr22p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr22p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr22p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr22p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr22p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr22p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr22p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr22p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr22p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr22p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr22p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr22p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr22p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have h:=sr22p15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
            · by_cases h16_18:V < 17
              · have h:=sr22p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr22p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have h:=sr22p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr22p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
            · by_cases h20_22:V < 21
              · have h:=sr22p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr22p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have h:=sr22p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr22p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
            · by_cases h24_26:V < 25
              · have h:=sr22p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr22p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have h:=sr22p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr22p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
            · by_cases h28_30:V < 29
              · have h:=sr22p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr22p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
    · by_cases h30_60:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have h:=sr22p30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
            · by_cases h31_33:V < 32
              · have h:=sr22p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr22p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have h:=sr22p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr22p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
            · by_cases h35_37:V < 36
              · have h:=sr22p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr22p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have h:=sr22p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr22p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
            · by_cases h39_41:V < 40
              · have h:=sr22p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr22p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have h:=sr22p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr22p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr22p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr22p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h45_60:V < 52
        · by_cases h45_52:V < 48
          · by_cases h45_48:V < 46
            · have h:=sr22p45 (V-45) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
            · by_cases h46_48:V < 47
              · have h:=sr22p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr22p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have h:=sr22p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr22p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
            · by_cases h50_52:V < 51
              · have h:=sr22p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr22p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
        · by_cases h52_60:V < 56
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have h:=sr22p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr22p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
            · by_cases h54_56:V < 55
              · have h:=sr22p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr22p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have h:=sr22p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr22p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
            · by_cases h58_60:V < 59
              · have h:=sr22p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr22p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
  · by_cases h60_121:V < 90
    · by_cases h60_90:V < 75
      · by_cases h60_75:V < 67
        · by_cases h60_67:V < 63
          · by_cases h60_63:V < 61
            · have h:=sr22p60 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · by_cases h61_63:V < 62
              · have h:=sr22p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr22p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
          · by_cases h63_67:V < 65
            · by_cases h63_65:V < 64
              · have h:=sr22p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr22p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
            · by_cases h65_67:V < 66
              · have h:=sr22p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr22p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
        · by_cases h67_75:V < 71
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have h:=sr22p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr22p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
            · by_cases h69_71:V < 70
              · have h:=sr22p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr22p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have h:=sr22p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr22p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
            · by_cases h73_75:V < 74
              · have h:=sr22p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr22p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
      · by_cases h75_90:V < 82
        · by_cases h75_82:V < 78
          · by_cases h75_78:V < 76
            · have h:=sr22p75 (V-75) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
            · by_cases h76_78:V < 77
              · have h:=sr22p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr22p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have h:=sr22p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr22p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
            · by_cases h80_82:V < 81
              · have h:=sr22p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr22p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have h:=sr22p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr22p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
            · by_cases h84_86:V < 85
              · have h:=sr22p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr22p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have h:=sr22p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr22p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
            · by_cases h88_90:V < 89
              · have h:=sr22p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr22p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
    · by_cases h90_121:V < 105
      · by_cases h90_105:V < 97
        · by_cases h90_97:V < 93
          · by_cases h90_93:V < 91
            · have h:=sr22p90 (V-90) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr22p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr22p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have h:=sr22p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr22p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
            · by_cases h95_97:V < 96
              · have h:=sr22p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr22p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · by_cases h97_105:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have h:=sr22p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr22p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_101:V < 100
              · have h:=sr22p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr22p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have h:=sr22p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr22p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr22p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr22p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h105_121:V < 113
        · by_cases h105_113:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have h:=sr22p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr22p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
            · by_cases h107_109:V < 108
              · have h:=sr22p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr22p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have h:=sr22p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr22p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
            · by_cases h111_113:V < 112
              · have h:=sr22p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr22p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h113_121:V < 117
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have h:=sr22p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr22p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
            · by_cases h115_117:V < 116
              · have h:=sr22p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr22p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · by_cases h117_121:V < 119
            · by_cases h117_119:V < 118
              · have h:=sr22p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
              · have h:=sr22p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
            · by_cases h119_121:V < 120
              · have h:=sr22p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
              · have h:=sr22p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem br22:∀ V ∈ List.range 121,BaseCheckAt 22 V:=by
  intro V hV
  have hv:V < 121:=List.mem_range.mp hV
  by_cases h0_31:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br22p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br22p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br22p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br22p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br22p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br22p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br22p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br22p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br22p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br22p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br22p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br22p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br22p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br22p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br22p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_31:V < 92
    · by_cases h15_23:V < 76
      · by_cases h15_19:V < 68
        · by_cases h15_17:V < 64
          · have h:=br22p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br22p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · by_cases h17_19:V < 72
          · have h:=br22p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br22p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h19_23:V < 84
        · by_cases h19_21:V < 80
          · have h:=br22p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br22p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · by_cases h21_23:V < 88
          · have h:=br22p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br22p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h23_31:V < 108
      · by_cases h23_27:V < 100
        · by_cases h23_25:V < 96
          · have h:=br22p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br22p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · by_cases h25_27:V < 104
          · have h:=br22p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br22p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h27_31:V < 116
        · by_cases h27_29:V < 112
          · have h:=br22p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br22p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h29_31:V < 120
          · have h:=br22p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · have h:=br22p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
