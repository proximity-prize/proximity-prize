import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr17p0:∀ i ∈ List.range 8,CorrectAt 17 (0+i):=by decide +kernel

theorem cr17p1:∀ i ∈ List.range 8,CorrectAt 17 (8+i):=by decide +kernel

theorem cr17p2:∀ i ∈ List.range 8,CorrectAt 17 (16+i):=by decide +kernel

theorem cr17p3:∀ i ∈ List.range 8,CorrectAt 17 (24+i):=by decide +kernel

theorem cr17p4:∀ i ∈ List.range 8,CorrectAt 17 (32+i):=by decide +kernel

theorem cr17p5:∀ i ∈ List.range 8,CorrectAt 17 (40+i):=by decide +kernel

theorem cr17p6:∀ i ∈ List.range 8,CorrectAt 17 (48+i):=by decide +kernel

theorem cr17p7:∀ i ∈ List.range 8,CorrectAt 17 (56+i):=by decide +kernel

theorem cr17p8:∀ i ∈ List.range 8,CorrectAt 17 (64+i):=by decide +kernel

theorem cr17p9:∀ i ∈ List.range 8,CorrectAt 17 (72+i):=by decide +kernel

theorem cr17p10:∀ i ∈ List.range 8,CorrectAt 17 (80+i):=by decide +kernel

theorem cr17p11:∀ i ∈ List.range 8,CorrectAt 17 (88+i):=by decide +kernel

theorem cr17p12:∀ i ∈ List.range 8,CorrectAt 17 (96+i):=by decide +kernel

theorem cr17p13:∀ i ∈ List.range 8,CorrectAt 17 (104+i):=by decide +kernel

theorem cr17p14:∀ i ∈ List.range 8,CorrectAt 17 (112+i):=by decide +kernel

theorem cr17p15:∀ i ∈ List.range 6,CorrectAt 17 (120+i):=by decide +kernel

theorem sr17p0:∀ i ∈ List.range 1,StrictCheckAt 17 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 0) 17 0:=by decide +kernel
  have hfast:StrictAtFast (row 17 0) 17 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 0) 17 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 0) 17 0 hvalid hfast

theorem sr17p1:∀ i ∈ List.range 1,StrictCheckAt 17 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 1) 17 1:=by decide +kernel
  have hfast:StrictAtFast (row 17 1) 17 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 1) 17 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 1) 17 1 hvalid hfast

theorem sr17p2:∀ i ∈ List.range 1,StrictCheckAt 17 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 2) 17 2:=by decide +kernel
  have hfast:StrictAtFast (row 17 2) 17 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 2) 17 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 2) 17 2 hvalid hfast

theorem sr17p3:∀ i ∈ List.range 1,StrictCheckAt 17 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 3) 17 3:=by decide +kernel
  have hfast:StrictAtFast (row 17 3) 17 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 3) 17 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 3) 17 3 hvalid hfast

theorem sr17p4:∀ i ∈ List.range 1,StrictCheckAt 17 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 4) 17 4:=by decide +kernel
  have hfast:StrictAtFast (row 17 4) 17 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 4) 17 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 4) 17 4 hvalid hfast

theorem sr17p5:∀ i ∈ List.range 1,StrictCheckAt 17 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 5) 17 5:=by decide +kernel
  have hfast:StrictAtFast (row 17 5) 17 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 5) 17 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 5) 17 5 hvalid hfast

theorem sr17p6:∀ i ∈ List.range 1,StrictCheckAt 17 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 6) 17 6:=by decide +kernel
  have hfast:StrictAtFast (row 17 6) 17 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 6) 17 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 6) 17 6 hvalid hfast

theorem sr17p7:∀ i ∈ List.range 1,StrictCheckAt 17 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 7) 17 7:=by decide +kernel
  have hfast:StrictAtFast (row 17 7) 17 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 7) 17 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 7) 17 7 hvalid hfast

theorem sr17p8:∀ i ∈ List.range 1,StrictCheckAt 17 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 8) 17 8:=by decide +kernel
  have hfast:StrictAtFast (row 17 8) 17 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 8) 17 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 8) 17 8 hvalid hfast

theorem sr17p9:∀ i ∈ List.range 1,StrictCheckAt 17 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 9) 17 9:=by decide +kernel
  have hfast:StrictAtFast (row 17 9) 17 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 9) 17 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 9) 17 9 hvalid hfast

theorem sr17p10:∀ i ∈ List.range 1,StrictCheckAt 17 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 10) 17 10:=by decide +kernel
  have hfast:StrictAtFast (row 17 10) 17 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 10) 17 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 10) 17 10 hvalid hfast

theorem sr17p11:∀ i ∈ List.range 1,StrictCheckAt 17 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 11) 17 11:=by decide +kernel
  have hfast:StrictAtFast (row 17 11) 17 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 11) 17 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 11) 17 11 hvalid hfast

theorem sr17p12:∀ i ∈ List.range 1,StrictCheckAt 17 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 12) 17 12:=by decide +kernel
  have hfast:StrictAtFast (row 17 12) 17 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 12) 17 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 12) 17 12 hvalid hfast

theorem sr17p13:∀ i ∈ List.range 1,StrictCheckAt 17 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 13) 17 13:=by decide +kernel
  have hfast:StrictAtFast (row 17 13) 17 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 13) 17 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 13) 17 13 hvalid hfast

theorem sr17p14:∀ i ∈ List.range 1,StrictCheckAt 17 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 14) 17 14:=by decide +kernel
  have hfast:StrictAtFast (row 17 14) 17 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 14) 17 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 14) 17 14 hvalid hfast

theorem sr17p15:∀ i ∈ List.range 1,StrictCheckAt 17 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 15) 17 15:=by decide +kernel
  have hfast:StrictAtFast (row 17 15) 17 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 15) 17 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 15) 17 15 hvalid hfast

theorem sr17p16:∀ i ∈ List.range 1,StrictCheckAt 17 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 16) 17 16:=by decide +kernel
  have hfast:StrictAtFast (row 17 16) 17 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 16) 17 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 16) 17 16 hvalid hfast

theorem sr17p17:∀ i ∈ List.range 1,StrictCheckAt 17 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 17) 17 17:=by decide +kernel
  have hfast:StrictAtFast (row 17 17) 17 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 17) 17 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 17) 17 17 hvalid hfast

theorem sr17p18:∀ i ∈ List.range 1,StrictCheckAt 17 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 18) 17 18:=by decide +kernel
  have hfast:StrictAtFast (row 17 18) 17 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 18) 17 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 18) 17 18 hvalid hfast

theorem sr17p19:∀ i ∈ List.range 1,StrictCheckAt 17 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 19) 17 19:=by decide +kernel
  have hfast:StrictAtFast (row 17 19) 17 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 19) 17 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 19) 17 19 hvalid hfast

theorem sr17p20:∀ i ∈ List.range 1,StrictCheckAt 17 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 20) 17 20:=by decide +kernel
  have hfast:StrictAtFast (row 17 20) 17 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 20) 17 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 20) 17 20 hvalid hfast

theorem sr17p21:∀ i ∈ List.range 1,StrictCheckAt 17 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 21) 17 21:=by decide +kernel
  have hfast:StrictAtFast (row 17 21) 17 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 21) 17 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 21) 17 21 hvalid hfast

theorem sr17p22:∀ i ∈ List.range 1,StrictCheckAt 17 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 22) 17 22:=by decide +kernel
  have hfast:StrictAtFast (row 17 22) 17 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 22) 17 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 22) 17 22 hvalid hfast

theorem sr17p23:∀ i ∈ List.range 1,StrictCheckAt 17 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 23) 17 23:=by decide +kernel
  have hfast:StrictAtFast (row 17 23) 17 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 23) 17 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 23) 17 23 hvalid hfast

theorem sr17p24:∀ i ∈ List.range 1,StrictCheckAt 17 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 24) 17 24:=by decide +kernel
  have hfast:StrictAtFast (row 17 24) 17 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 24) 17 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 24) 17 24 hvalid hfast

theorem sr17p25:∀ i ∈ List.range 1,StrictCheckAt 17 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 25) 17 25:=by decide +kernel
  have hfast:StrictAtFast (row 17 25) 17 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 25) 17 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 25) 17 25 hvalid hfast

theorem sr17p26:∀ i ∈ List.range 1,StrictCheckAt 17 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 26) 17 26:=by decide +kernel
  have hfast:StrictAtFast (row 17 26) 17 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 26) 17 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 26) 17 26 hvalid hfast

theorem sr17p27:∀ i ∈ List.range 1,StrictCheckAt 17 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 27) 17 27:=by decide +kernel
  have hfast:StrictAtFast (row 17 27) 17 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 27) 17 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 27) 17 27 hvalid hfast

theorem sr17p28:∀ i ∈ List.range 1,StrictCheckAt 17 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 28) 17 28:=by decide +kernel
  have hfast:StrictAtFast (row 17 28) 17 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 28) 17 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 28) 17 28 hvalid hfast

theorem sr17p29:∀ i ∈ List.range 1,StrictCheckAt 17 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 29) 17 29:=by decide +kernel
  have hfast:StrictAtFast (row 17 29) 17 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 29) 17 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 29) 17 29 hvalid hfast

theorem sr17p30:∀ i ∈ List.range 1,StrictCheckAt 17 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 30) 17 30:=by decide +kernel
  have hfast:StrictAtFast (row 17 30) 17 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 30) 17 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 30) 17 30 hvalid hfast

theorem sr17p31:∀ i ∈ List.range 1,StrictCheckAt 17 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 31) 17 31:=by decide +kernel
  have hfast:StrictAtFast (row 17 31) 17 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 31) 17 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 31) 17 31 hvalid hfast

theorem sr17p32:∀ i ∈ List.range 1,StrictCheckAt 17 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 32) 17 32:=by decide +kernel
  have hfast:StrictAtFast (row 17 32) 17 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 32) 17 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 32) 17 32 hvalid hfast

theorem sr17p33:∀ i ∈ List.range 1,StrictCheckAt 17 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 33) 17 33:=by decide +kernel
  have hfast:StrictAtFast (row 17 33) 17 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 33) 17 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 33) 17 33 hvalid hfast

theorem sr17p34:∀ i ∈ List.range 1,StrictCheckAt 17 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 34) 17 34:=by decide +kernel
  have hfast:StrictAtFast (row 17 34) 17 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 34) 17 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 34) 17 34 hvalid hfast

theorem sr17p35:∀ i ∈ List.range 1,StrictCheckAt 17 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 35) 17 35:=by decide +kernel
  have hfast:StrictAtFast (row 17 35) 17 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 35) 17 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 35) 17 35 hvalid hfast

theorem sr17p36:∀ i ∈ List.range 1,StrictCheckAt 17 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 36) 17 36:=by decide +kernel
  have hfast:StrictAtFast (row 17 36) 17 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 36) 17 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 36) 17 36 hvalid hfast

theorem sr17p37:∀ i ∈ List.range 1,StrictCheckAt 17 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 37) 17 37:=by decide +kernel
  have hfast:StrictAtFast (row 17 37) 17 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 37) 17 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 37) 17 37 hvalid hfast

theorem sr17p38:∀ i ∈ List.range 1,StrictCheckAt 17 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 38) 17 38:=by decide +kernel
  have hfast:StrictAtFast (row 17 38) 17 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 38) 17 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 38) 17 38 hvalid hfast

theorem sr17p39:∀ i ∈ List.range 1,StrictCheckAt 17 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 39) 17 39:=by decide +kernel
  have hfast:StrictAtFast (row 17 39) 17 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 39) 17 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 39) 17 39 hvalid hfast

theorem sr17p40:∀ i ∈ List.range 1,StrictCheckAt 17 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 40) 17 40:=by decide +kernel
  have hfast:StrictAtFast (row 17 40) 17 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 40) 17 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 40) 17 40 hvalid hfast

theorem sr17p41:∀ i ∈ List.range 1,StrictCheckAt 17 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 41) 17 41:=by decide +kernel
  have hfast:StrictAtFast (row 17 41) 17 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 41) 17 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 41) 17 41 hvalid hfast

theorem sr17p42:∀ i ∈ List.range 1,StrictCheckAt 17 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 42) 17 42:=by decide +kernel
  have hfast:StrictAtFast (row 17 42) 17 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 42) 17 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 42) 17 42 hvalid hfast

theorem sr17p43:∀ i ∈ List.range 1,StrictCheckAt 17 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 43) 17 43:=by decide +kernel
  have hfast:StrictAtFast (row 17 43) 17 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 43) 17 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 43) 17 43 hvalid hfast

theorem sr17p44:∀ i ∈ List.range 1,StrictCheckAt 17 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 44) 17 44:=by decide +kernel
  have hfast:StrictAtFast (row 17 44) 17 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 44) 17 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 44) 17 44 hvalid hfast

theorem sr17p45:∀ i ∈ List.range 1,StrictCheckAt 17 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 45) 17 45:=by decide +kernel
  have hfast:StrictAtFast (row 17 45) 17 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 45) 17 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 45) 17 45 hvalid hfast

theorem sr17p46:∀ i ∈ List.range 1,StrictCheckAt 17 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 46) 17 46:=by decide +kernel
  have hfast:StrictAtFast (row 17 46) 17 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 46) 17 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 46) 17 46 hvalid hfast

theorem sr17p47:∀ i ∈ List.range 1,StrictCheckAt 17 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 47) 17 47:=by decide +kernel
  have hfast:StrictAtFast (row 17 47) 17 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 47) 17 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 47) 17 47 hvalid hfast

theorem sr17p48:∀ i ∈ List.range 1,StrictCheckAt 17 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 48) 17 48:=by decide +kernel
  have hfast:StrictAtFast (row 17 48) 17 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 48) 17 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 48) 17 48 hvalid hfast

theorem sr17p49:∀ i ∈ List.range 1,StrictCheckAt 17 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 49) 17 49:=by decide +kernel
  have hfast:StrictAtFast (row 17 49) 17 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 49) 17 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 49) 17 49 hvalid hfast

theorem sr17p50:∀ i ∈ List.range 1,StrictCheckAt 17 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 50) 17 50:=by decide +kernel
  have hfast:StrictAtFast (row 17 50) 17 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 50) 17 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 50) 17 50 hvalid hfast

theorem sr17p51:∀ i ∈ List.range 1,StrictCheckAt 17 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 51) 17 51:=by decide +kernel
  have hfast:StrictAtFast (row 17 51) 17 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 51) 17 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 51) 17 51 hvalid hfast

theorem sr17p52:∀ i ∈ List.range 1,StrictCheckAt 17 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 52) 17 52:=by decide +kernel
  have hfast:StrictAtFast (row 17 52) 17 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 52) 17 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 52) 17 52 hvalid hfast

theorem sr17p53:∀ i ∈ List.range 1,StrictCheckAt 17 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 53) 17 53:=by decide +kernel
  have hfast:StrictAtFast (row 17 53) 17 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 53) 17 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 53) 17 53 hvalid hfast

theorem sr17p54:∀ i ∈ List.range 1,StrictCheckAt 17 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 54) 17 54:=by decide +kernel
  have hfast:StrictAtFast (row 17 54) 17 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 54) 17 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 54) 17 54 hvalid hfast

theorem sr17p55:∀ i ∈ List.range 1,StrictCheckAt 17 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 55) 17 55:=by decide +kernel
  have hfast:StrictAtFast (row 17 55) 17 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 55) 17 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 55) 17 55 hvalid hfast

theorem sr17p56:∀ i ∈ List.range 1,StrictCheckAt 17 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 56) 17 56:=by decide +kernel
  have hfast:StrictAtFast (row 17 56) 17 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 56) 17 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 56) 17 56 hvalid hfast

theorem sr17p57:∀ i ∈ List.range 1,StrictCheckAt 17 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 57) 17 57:=by decide +kernel
  have hfast:StrictAtFast (row 17 57) 17 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 57) 17 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 57) 17 57 hvalid hfast

theorem sr17p58:∀ i ∈ List.range 1,StrictCheckAt 17 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 58) 17 58:=by decide +kernel
  have hfast:StrictAtFast (row 17 58) 17 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 58) 17 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 58) 17 58 hvalid hfast

theorem sr17p59:∀ i ∈ List.range 1,StrictCheckAt 17 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 59) 17 59:=by decide +kernel
  have hfast:StrictAtFast (row 17 59) 17 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 59) 17 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 59) 17 59 hvalid hfast

theorem sr17p60:∀ i ∈ List.range 1,StrictCheckAt 17 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 60) 17 60:=by decide +kernel
  have hfast:StrictAtFast (row 17 60) 17 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 60) 17 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 60) 17 60 hvalid hfast

theorem sr17p61:∀ i ∈ List.range 1,StrictCheckAt 17 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 61) 17 61:=by decide +kernel
  have hfast:StrictAtFast (row 17 61) 17 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 61) 17 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 61) 17 61 hvalid hfast

theorem sr17p62:∀ i ∈ List.range 1,StrictCheckAt 17 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 62) 17 62:=by decide +kernel
  have hfast:StrictAtFast (row 17 62) 17 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 62) 17 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 62) 17 62 hvalid hfast

theorem sr17p63:∀ i ∈ List.range 1,StrictCheckAt 17 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 63) 17 63:=by decide +kernel
  have hfast:StrictAtFast (row 17 63) 17 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 63) 17 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 63) 17 63 hvalid hfast

theorem sr17p64:∀ i ∈ List.range 1,StrictCheckAt 17 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 64) 17 64:=by decide +kernel
  have hfast:StrictAtFast (row 17 64) 17 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 64) 17 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 64) 17 64 hvalid hfast

theorem sr17p65:∀ i ∈ List.range 1,StrictCheckAt 17 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 65) 17 65:=by decide +kernel
  have hfast:StrictAtFast (row 17 65) 17 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 65) 17 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 65) 17 65 hvalid hfast

theorem sr17p66:∀ i ∈ List.range 1,StrictCheckAt 17 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 66) 17 66:=by decide +kernel
  have hfast:StrictAtFast (row 17 66) 17 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 66) 17 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 66) 17 66 hvalid hfast

theorem sr17p67:∀ i ∈ List.range 1,StrictCheckAt 17 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 67) 17 67:=by decide +kernel
  have hfast:StrictAtFast (row 17 67) 17 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 67) 17 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 67) 17 67 hvalid hfast

theorem sr17p68:∀ i ∈ List.range 1,StrictCheckAt 17 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 68) 17 68:=by decide +kernel
  have hfast:StrictAtFast (row 17 68) 17 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 68) 17 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 68) 17 68 hvalid hfast

theorem sr17p69:∀ i ∈ List.range 1,StrictCheckAt 17 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 69) 17 69:=by decide +kernel
  have hfast:StrictAtFast (row 17 69) 17 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 69) 17 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 69) 17 69 hvalid hfast

theorem sr17p70:∀ i ∈ List.range 1,StrictCheckAt 17 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 70) 17 70:=by decide +kernel
  have hfast:StrictAtFast (row 17 70) 17 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 70) 17 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 70) 17 70 hvalid hfast

theorem sr17p71:∀ i ∈ List.range 1,StrictCheckAt 17 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 71) 17 71:=by decide +kernel
  have hfast:StrictAtFast (row 17 71) 17 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 71) 17 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 71) 17 71 hvalid hfast

theorem sr17p72:∀ i ∈ List.range 1,StrictCheckAt 17 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 72) 17 72:=by decide +kernel
  have hfast:StrictAtFast (row 17 72) 17 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 72) 17 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 72) 17 72 hvalid hfast

theorem sr17p73:∀ i ∈ List.range 1,StrictCheckAt 17 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 73) 17 73:=by decide +kernel
  have hfast:StrictAtFast (row 17 73) 17 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 73) 17 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 73) 17 73 hvalid hfast

theorem sr17p74:∀ i ∈ List.range 1,StrictCheckAt 17 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 74) 17 74:=by decide +kernel
  have hfast:StrictAtFast (row 17 74) 17 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 74) 17 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 74) 17 74 hvalid hfast

theorem sr17p75:∀ i ∈ List.range 1,StrictCheckAt 17 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 75) 17 75:=by decide +kernel
  have hfast:StrictAtFast (row 17 75) 17 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 75) 17 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 75) 17 75 hvalid hfast

theorem sr17p76:∀ i ∈ List.range 1,StrictCheckAt 17 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 76) 17 76:=by decide +kernel
  have hfast:StrictAtFast (row 17 76) 17 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 76) 17 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 76) 17 76 hvalid hfast

theorem sr17p77:∀ i ∈ List.range 1,StrictCheckAt 17 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 77) 17 77:=by decide +kernel
  have hfast:StrictAtFast (row 17 77) 17 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 77) 17 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 77) 17 77 hvalid hfast

theorem sr17p78:∀ i ∈ List.range 1,StrictCheckAt 17 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 78) 17 78:=by decide +kernel
  have hfast:StrictAtFast (row 17 78) 17 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 78) 17 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 78) 17 78 hvalid hfast

theorem sr17p79:∀ i ∈ List.range 1,StrictCheckAt 17 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 79) 17 79:=by decide +kernel
  have hfast:StrictAtFast (row 17 79) 17 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 79) 17 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 79) 17 79 hvalid hfast

theorem sr17p80:∀ i ∈ List.range 1,StrictCheckAt 17 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 80) 17 80:=by decide +kernel
  have hfast:StrictAtFast (row 17 80) 17 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 80) 17 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 80) 17 80 hvalid hfast

theorem sr17p81:∀ i ∈ List.range 1,StrictCheckAt 17 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 81) 17 81:=by decide +kernel
  have hfast:StrictAtFast (row 17 81) 17 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 81) 17 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 81) 17 81 hvalid hfast

theorem sr17p82:∀ i ∈ List.range 1,StrictCheckAt 17 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 82) 17 82:=by decide +kernel
  have hfast:StrictAtFast (row 17 82) 17 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 82) 17 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 82) 17 82 hvalid hfast

theorem sr17p83:∀ i ∈ List.range 1,StrictCheckAt 17 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 83) 17 83:=by decide +kernel
  have hfast:StrictAtFast (row 17 83) 17 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 83) 17 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 83) 17 83 hvalid hfast

theorem sr17p84:∀ i ∈ List.range 1,StrictCheckAt 17 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 84) 17 84:=by decide +kernel
  have hfast:StrictAtFast (row 17 84) 17 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 84) 17 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 84) 17 84 hvalid hfast

theorem sr17p85:∀ i ∈ List.range 1,StrictCheckAt 17 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 85) 17 85:=by decide +kernel
  have hfast:StrictAtFast (row 17 85) 17 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 85) 17 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 85) 17 85 hvalid hfast

theorem sr17p86:∀ i ∈ List.range 1,StrictCheckAt 17 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 86) 17 86:=by decide +kernel
  have hfast:StrictAtFast (row 17 86) 17 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 86) 17 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 86) 17 86 hvalid hfast

theorem sr17p87:∀ i ∈ List.range 1,StrictCheckAt 17 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 87) 17 87:=by decide +kernel
  have hfast:StrictAtFast (row 17 87) 17 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 87) 17 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 87) 17 87 hvalid hfast

theorem sr17p88:∀ i ∈ List.range 1,StrictCheckAt 17 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 88) 17 88:=by decide +kernel
  have hfast:StrictAtFast (row 17 88) 17 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 88) 17 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 88) 17 88 hvalid hfast

theorem sr17p89:∀ i ∈ List.range 1,StrictCheckAt 17 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 89) 17 89:=by decide +kernel
  have hfast:StrictAtFast (row 17 89) 17 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 89) 17 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 89) 17 89 hvalid hfast

theorem sr17p90:∀ i ∈ List.range 1,StrictCheckAt 17 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 90) 17 90:=by decide +kernel
  have hfast:StrictAtFast (row 17 90) 17 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 90) 17 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 90) 17 90 hvalid hfast

theorem sr17p91:∀ i ∈ List.range 1,StrictCheckAt 17 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 91) 17 91:=by decide +kernel
  have hfast:StrictAtFast (row 17 91) 17 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 91) 17 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 91) 17 91 hvalid hfast

theorem sr17p92:∀ i ∈ List.range 1,StrictCheckAt 17 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 92) 17 92:=by decide +kernel
  have hfast:StrictAtFast (row 17 92) 17 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 92) 17 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 92) 17 92 hvalid hfast

theorem sr17p93:∀ i ∈ List.range 1,StrictCheckAt 17 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 93) 17 93:=by decide +kernel
  have hfast:StrictAtFast (row 17 93) 17 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 93) 17 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 93) 17 93 hvalid hfast

theorem sr17p94:∀ i ∈ List.range 1,StrictCheckAt 17 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 94) 17 94:=by decide +kernel
  have hfast:StrictAtFast (row 17 94) 17 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 94) 17 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 94) 17 94 hvalid hfast

theorem sr17p95:∀ i ∈ List.range 1,StrictCheckAt 17 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 95) 17 95:=by decide +kernel
  have hfast:StrictAtFast (row 17 95) 17 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 95) 17 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 95) 17 95 hvalid hfast

theorem sr17p96:∀ i ∈ List.range 1,StrictCheckAt 17 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 96) 17 96:=by decide +kernel
  have hfast:StrictAtFast (row 17 96) 17 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 96) 17 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 96) 17 96 hvalid hfast

theorem sr17p97:∀ i ∈ List.range 1,StrictCheckAt 17 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 97) 17 97:=by decide +kernel
  have hfast:StrictAtFast (row 17 97) 17 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 97) 17 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 97) 17 97 hvalid hfast

theorem sr17p98:∀ i ∈ List.range 1,StrictCheckAt 17 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 98) 17 98:=by decide +kernel
  have hfast:StrictAtFast (row 17 98) 17 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 98) 17 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 98) 17 98 hvalid hfast

theorem sr17p99:∀ i ∈ List.range 1,StrictCheckAt 17 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 99) 17 99:=by decide +kernel
  have hfast:StrictAtFast (row 17 99) 17 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 99) 17 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 99) 17 99 hvalid hfast

theorem sr17p100:∀ i ∈ List.range 1,StrictCheckAt 17 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 100) 17 100:=by decide +kernel
  have hfast:StrictAtFast (row 17 100) 17 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 100) 17 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 100) 17 100 hvalid hfast

theorem sr17p101:∀ i ∈ List.range 1,StrictCheckAt 17 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 101) 17 101:=by decide +kernel
  have hfast:StrictAtFast (row 17 101) 17 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 101) 17 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 101) 17 101 hvalid hfast

theorem sr17p102:∀ i ∈ List.range 1,StrictCheckAt 17 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 102) 17 102:=by decide +kernel
  have hfast:StrictAtFast (row 17 102) 17 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 102) 17 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 102) 17 102 hvalid hfast

theorem sr17p103:∀ i ∈ List.range 1,StrictCheckAt 17 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 103) 17 103:=by decide +kernel
  have hfast:StrictAtFast (row 17 103) 17 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 103) 17 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 103) 17 103 hvalid hfast

theorem sr17p104:∀ i ∈ List.range 1,StrictCheckAt 17 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 104) 17 104:=by decide +kernel
  have hfast:StrictAtFast (row 17 104) 17 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 104) 17 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 104) 17 104 hvalid hfast

theorem sr17p105:∀ i ∈ List.range 1,StrictCheckAt 17 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 105) 17 105:=by decide +kernel
  have hfast:StrictAtFast (row 17 105) 17 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 105) 17 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 105) 17 105 hvalid hfast

theorem sr17p106:∀ i ∈ List.range 1,StrictCheckAt 17 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 106) 17 106:=by decide +kernel
  have hfast:StrictAtFast (row 17 106) 17 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 106) 17 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 106) 17 106 hvalid hfast

theorem sr17p107:∀ i ∈ List.range 1,StrictCheckAt 17 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 107) 17 107:=by decide +kernel
  have hfast:StrictAtFast (row 17 107) 17 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 107) 17 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 107) 17 107 hvalid hfast

theorem sr17p108:∀ i ∈ List.range 1,StrictCheckAt 17 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 108) 17 108:=by decide +kernel
  have hfast:StrictAtFast (row 17 108) 17 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 108) 17 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 108) 17 108 hvalid hfast

theorem sr17p109:∀ i ∈ List.range 1,StrictCheckAt 17 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 109) 17 109:=by decide +kernel
  have hfast:StrictAtFast (row 17 109) 17 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 109) 17 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 109) 17 109 hvalid hfast

theorem sr17p110:∀ i ∈ List.range 1,StrictCheckAt 17 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 110) 17 110:=by decide +kernel
  have hfast:StrictAtFast (row 17 110) 17 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 110) 17 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 110) 17 110 hvalid hfast

theorem sr17p111:∀ i ∈ List.range 1,StrictCheckAt 17 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 111) 17 111:=by decide +kernel
  have hfast:StrictAtFast (row 17 111) 17 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 111) 17 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 111) 17 111 hvalid hfast

theorem sr17p112:∀ i ∈ List.range 1,StrictCheckAt 17 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 112) 17 112:=by decide +kernel
  have hfast:StrictAtFast (row 17 112) 17 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 112) 17 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 112) 17 112 hvalid hfast

theorem sr17p113:∀ i ∈ List.range 1,StrictCheckAt 17 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 113) 17 113:=by decide +kernel
  have hfast:StrictAtFast (row 17 113) 17 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 113) 17 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 113) 17 113 hvalid hfast

theorem sr17p114:∀ i ∈ List.range 1,StrictCheckAt 17 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 114) 17 114:=by decide +kernel
  have hfast:StrictAtFast (row 17 114) 17 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 114) 17 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 114) 17 114 hvalid hfast

theorem sr17p115:∀ i ∈ List.range 1,StrictCheckAt 17 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 115) 17 115:=by decide +kernel
  have hfast:StrictAtFast (row 17 115) 17 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 115) 17 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 115) 17 115 hvalid hfast

theorem sr17p116:∀ i ∈ List.range 1,StrictCheckAt 17 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 116) 17 116:=by decide +kernel
  have hfast:StrictAtFast (row 17 116) 17 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 116) 17 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 116) 17 116 hvalid hfast

theorem sr17p117:∀ i ∈ List.range 1,StrictCheckAt 17 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 117) 17 117:=by decide +kernel
  have hfast:StrictAtFast (row 17 117) 17 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 117) 17 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 117) 17 117 hvalid hfast

theorem sr17p118:∀ i ∈ List.range 1,StrictCheckAt 17 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 118) 17 118:=by decide +kernel
  have hfast:StrictAtFast (row 17 118) 17 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 118) 17 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 118) 17 118 hvalid hfast

theorem sr17p119:∀ i ∈ List.range 1,StrictCheckAt 17 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 119) 17 119:=by decide +kernel
  have hfast:StrictAtFast (row 17 119) 17 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 119) 17 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 119) 17 119 hvalid hfast

theorem sr17p120:∀ i ∈ List.range 1,StrictCheckAt 17 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 120) 17 120:=by decide +kernel
  have hfast:StrictAtFast (row 17 120) 17 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 120) 17 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 120) 17 120 hvalid hfast

theorem sr17p121:∀ i ∈ List.range 1,StrictCheckAt 17 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 121) 17 121:=by decide +kernel
  have hfast:StrictAtFast (row 17 121) 17 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 121) 17 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 121) 17 121 hvalid hfast

theorem sr17p122:∀ i ∈ List.range 1,StrictCheckAt 17 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 122) 17 122:=by decide +kernel
  have hfast:StrictAtFast (row 17 122) 17 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 122) 17 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 122) 17 122 hvalid hfast

theorem sr17p123:∀ i ∈ List.range 1,StrictCheckAt 17 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 123) 17 123:=by decide +kernel
  have hfast:StrictAtFast (row 17 123) 17 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 123) 17 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 123) 17 123 hvalid hfast

theorem sr17p124:∀ i ∈ List.range 1,StrictCheckAt 17 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 124) 17 124:=by decide +kernel
  have hfast:StrictAtFast (row 17 124) 17 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 124) 17 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 124) 17 124 hvalid hfast

theorem sr17p125:∀ i ∈ List.range 1,StrictCheckAt 17 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 17 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 17 125) 17 125:=by decide +kernel
  have hfast:StrictAtFast (row 17 125) 17 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 17 125) 17 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 17 125) 17 125 hvalid hfast

theorem br17p0:∀ i ∈ List.range 4,BaseCheckAt 17 (0+i):=by decide +kernel

theorem br17p1:∀ i ∈ List.range 4,BaseCheckAt 17 (4+i):=by decide +kernel

theorem br17p2:∀ i ∈ List.range 4,BaseCheckAt 17 (8+i):=by decide +kernel

theorem br17p3:∀ i ∈ List.range 4,BaseCheckAt 17 (12+i):=by decide +kernel

theorem br17p4:∀ i ∈ List.range 4,BaseCheckAt 17 (16+i):=by decide +kernel

theorem br17p5:∀ i ∈ List.range 4,BaseCheckAt 17 (20+i):=by decide +kernel

theorem br17p6:∀ i ∈ List.range 4,BaseCheckAt 17 (24+i):=by decide +kernel

theorem br17p7:∀ i ∈ List.range 4,BaseCheckAt 17 (28+i):=by decide +kernel

theorem br17p8:∀ i ∈ List.range 4,BaseCheckAt 17 (32+i):=by decide +kernel

theorem br17p9:∀ i ∈ List.range 4,BaseCheckAt 17 (36+i):=by decide +kernel

theorem br17p10:∀ i ∈ List.range 4,BaseCheckAt 17 (40+i):=by decide +kernel

theorem br17p11:∀ i ∈ List.range 4,BaseCheckAt 17 (44+i):=by decide +kernel

theorem br17p12:∀ i ∈ List.range 4,BaseCheckAt 17 (48+i):=by decide +kernel

theorem br17p13:∀ i ∈ List.range 4,BaseCheckAt 17 (52+i):=by decide +kernel

theorem br17p14:∀ i ∈ List.range 4,BaseCheckAt 17 (56+i):=by decide +kernel

theorem br17p15:∀ i ∈ List.range 4,BaseCheckAt 17 (60+i):=by decide +kernel



theorem br17p16:∀ i ∈ List.range 4,BaseCheckAt 17 (64+i):=by decide +kernel

theorem br17p17:∀ i ∈ List.range 4,BaseCheckAt 17 (68+i):=by decide +kernel

theorem br17p18:∀ i ∈ List.range 4,BaseCheckAt 17 (72+i):=by decide +kernel

theorem br17p19:∀ i ∈ List.range 4,BaseCheckAt 17 (76+i):=by decide +kernel

theorem br17p20:∀ i ∈ List.range 4,BaseCheckAt 17 (80+i):=by decide +kernel

theorem br17p21:∀ i ∈ List.range 4,BaseCheckAt 17 (84+i):=by decide +kernel

theorem br17p22:∀ i ∈ List.range 4,BaseCheckAt 17 (88+i):=by decide +kernel

theorem br17p23:∀ i ∈ List.range 4,BaseCheckAt 17 (92+i):=by decide +kernel

theorem br17p24:∀ i ∈ List.range 4,BaseCheckAt 17 (96+i):=by decide +kernel

theorem br17p25:∀ i ∈ List.range 4,BaseCheckAt 17 (100+i):=by decide +kernel

theorem br17p26:∀ i ∈ List.range 4,BaseCheckAt 17 (104+i):=by decide +kernel

theorem br17p27:∀ i ∈ List.range 4,BaseCheckAt 17 (108+i):=by decide +kernel

theorem br17p28:∀ i ∈ List.range 4,BaseCheckAt 17 (112+i):=by decide +kernel

theorem br17p29:∀ i ∈ List.range 4,BaseCheckAt 17 (116+i):=by decide +kernel

theorem br17p30:∀ i ∈ List.range 4,BaseCheckAt 17 (120+i):=by decide +kernel

theorem br17p31:∀ i ∈ List.range 2,BaseCheckAt 17 (124+i):=by decide +kernel



theorem cr17:∀ V ∈ List.range 126,CorrectAt 17 V:=by
  intro V hV
  have hv:V < 126:=List.mem_range.mp hV
  by_cases h0_16:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr17p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr17p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr17p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr17p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr17p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr17p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr17p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr17p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_16:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr17p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr17p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr17p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr17p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_16:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr17p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr17p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_16:V < 120
        · have h:=cr17p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · have h:=cr17p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem zr17:∀ V ∈ List.range 126,ZeroCheckAt 17 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 17 V (by omega) (by omega) (by omega)
theorem sr17:∀ V ∈ List.range 126,StrictCheckAt 17 V:=by
  intro V hV
  have hv:V < 126:=List.mem_range.mp hV
  by_cases h0_126:V < 63
  · by_cases h0_63:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr17p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr17p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr17p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr17p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr17p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr17p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr17p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr17p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr17p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr17p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr17p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr17p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr17p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr17p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr17p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have h:=sr17p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr17p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
            · by_cases h17_19:V < 18
              · have h:=sr17p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr17p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have h:=sr17p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr17p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
            · by_cases h21_23:V < 22
              · have h:=sr17p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr17p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have h:=sr17p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr17p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
            · by_cases h25_27:V < 26
              · have h:=sr17p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr17p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have h:=sr17p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr17p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr17p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr17p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
    · by_cases h31_63:V < 47
      · by_cases h31_47:V < 39
        · by_cases h31_39:V < 35
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have h:=sr17p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr17p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
            · by_cases h33_35:V < 34
              · have h:=sr17p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr17p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have h:=sr17p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr17p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
            · by_cases h37_39:V < 38
              · have h:=sr17p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr17p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
        · by_cases h39_47:V < 43
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have h:=sr17p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr17p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
            · by_cases h41_43:V < 42
              · have h:=sr17p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr17p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
          · by_cases h43_47:V < 45
            · by_cases h43_45:V < 44
              · have h:=sr17p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr17p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
            · by_cases h45_47:V < 46
              · have h:=sr17p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr17p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
      · by_cases h47_63:V < 55
        · by_cases h47_55:V < 51
          · by_cases h47_51:V < 49
            · by_cases h47_49:V < 48
              · have h:=sr17p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr17p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
            · by_cases h49_51:V < 50
              · have h:=sr17p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr17p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have h:=sr17p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr17p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
            · by_cases h53_55:V < 54
              · have h:=sr17p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr17p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
        · by_cases h55_63:V < 59
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have h:=sr17p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr17p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
            · by_cases h57_59:V < 58
              · have h:=sr17p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr17p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have h:=sr17p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr17p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · by_cases h61_63:V < 62
              · have h:=sr17p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr17p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
  · by_cases h63_126:V < 94
    · by_cases h63_94:V < 78
      · by_cases h63_78:V < 70
        · by_cases h63_70:V < 66
          · by_cases h63_66:V < 64
            · have h:=sr17p63 (V-63) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
            · by_cases h64_66:V < 65
              · have h:=sr17p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr17p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have h:=sr17p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr17p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
            · by_cases h68_70:V < 69
              · have h:=sr17p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr17p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
        · by_cases h70_78:V < 74
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have h:=sr17p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr17p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
            · by_cases h72_74:V < 73
              · have h:=sr17p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr17p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have h:=sr17p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr17p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
            · by_cases h76_78:V < 77
              · have h:=sr17p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr17p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
      · by_cases h78_94:V < 86
        · by_cases h78_86:V < 82
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have h:=sr17p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr17p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
            · by_cases h80_82:V < 81
              · have h:=sr17p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr17p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have h:=sr17p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr17p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
            · by_cases h84_86:V < 85
              · have h:=sr17p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr17p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
        · by_cases h86_94:V < 90
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have h:=sr17p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr17p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
            · by_cases h88_90:V < 89
              · have h:=sr17p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr17p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have h:=sr17p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr17p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr17p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr17p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
    · by_cases h94_126:V < 110
      · by_cases h94_110:V < 102
        · by_cases h94_102:V < 98
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have h:=sr17p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr17p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
            · by_cases h96_98:V < 97
              · have h:=sr17p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr17p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
          · by_cases h98_102:V < 100
            · by_cases h98_100:V < 99
              · have h:=sr17p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr17p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
            · by_cases h100_102:V < 101
              · have h:=sr17p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr17p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
        · by_cases h102_110:V < 106
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have h:=sr17p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr17p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
            · by_cases h104_106:V < 105
              · have h:=sr17p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr17p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have h:=sr17p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr17p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
            · by_cases h108_110:V < 109
              · have h:=sr17p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr17p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
      · by_cases h110_126:V < 118
        · by_cases h110_118:V < 114
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have h:=sr17p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr17p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
            · by_cases h112_114:V < 113
              · have h:=sr17p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr17p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have h:=sr17p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr17p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
            · by_cases h116_118:V < 117
              · have h:=sr17p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr17p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
        · by_cases h118_126:V < 122
          · by_cases h118_122:V < 120
            · by_cases h118_120:V < 119
              · have h:=sr17p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr17p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
            · by_cases h120_122:V < 121
              · have h:=sr17p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
              · have h:=sr17p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
          · by_cases h122_126:V < 124
            · by_cases h122_124:V < 123
              · have h:=sr17p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
              · have h:=sr17p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
            · by_cases h124_126:V < 125
              · have h:=sr17p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
              · have h:=sr17p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h

theorem br17:∀ V ∈ List.range 126,BaseCheckAt 17 V:=by
  intro V hV
  have hv:V < 126:=List.mem_range.mp hV
  by_cases h0_32:V < 64
  · by_cases h0_16:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br17p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br17p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br17p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br17p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br17p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br17p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br17p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br17p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_16:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br17p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br17p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br17p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br17p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_16:V < 56
        · by_cases h12_14:V < 52
          · have h:=br17p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br17p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_16:V < 60
          · have h:=br17p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · have h:=br17p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h16_32:V < 96
    · by_cases h16_24:V < 80
      · by_cases h16_20:V < 72
        · by_cases h16_18:V < 68
          · have h:=br17p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br17p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h18_20:V < 76
          · have h:=br17p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br17p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h20_24:V < 88
        · by_cases h20_22:V < 84
          · have h:=br17p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br17p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br17p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br17p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h24_32:V < 112
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br17p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br17p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br17p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br17p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h28_32:V < 120
        · by_cases h28_30:V < 116
          · have h:=br17p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br17p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h30_32:V < 124
          · have h:=br17p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=br17p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
