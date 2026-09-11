import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr19p0:∀ i ∈ List.range 8,CorrectAt 19 (0+i):=by decide +kernel

theorem cr19p1:∀ i ∈ List.range 8,CorrectAt 19 (8+i):=by decide +kernel

theorem cr19p2:∀ i ∈ List.range 8,CorrectAt 19 (16+i):=by decide +kernel

theorem cr19p3:∀ i ∈ List.range 8,CorrectAt 19 (24+i):=by decide +kernel

theorem cr19p4:∀ i ∈ List.range 8,CorrectAt 19 (32+i):=by decide +kernel

theorem cr19p5:∀ i ∈ List.range 8,CorrectAt 19 (40+i):=by decide +kernel

theorem cr19p6:∀ i ∈ List.range 8,CorrectAt 19 (48+i):=by decide +kernel

theorem cr19p7:∀ i ∈ List.range 8,CorrectAt 19 (56+i):=by decide +kernel

theorem cr19p8:∀ i ∈ List.range 8,CorrectAt 19 (64+i):=by decide +kernel

theorem cr19p9:∀ i ∈ List.range 8,CorrectAt 19 (72+i):=by decide +kernel

theorem cr19p10:∀ i ∈ List.range 8,CorrectAt 19 (80+i):=by decide +kernel

theorem cr19p11:∀ i ∈ List.range 8,CorrectAt 19 (88+i):=by decide +kernel

theorem cr19p12:∀ i ∈ List.range 8,CorrectAt 19 (96+i):=by decide +kernel

theorem cr19p13:∀ i ∈ List.range 8,CorrectAt 19 (104+i):=by decide +kernel

theorem cr19p14:∀ i ∈ List.range 8,CorrectAt 19 (112+i):=by decide +kernel

theorem cr19p15:∀ i ∈ List.range 4,CorrectAt 19 (120+i):=by decide +kernel

theorem sr19p0:∀ i ∈ List.range 1,StrictCheckAt 19 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 0) 19 0:=by decide +kernel
  have hfast:StrictAtFast (row 19 0) 19 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 0) 19 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 0) 19 0 hvalid hfast

theorem sr19p1:∀ i ∈ List.range 1,StrictCheckAt 19 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 1) 19 1:=by decide +kernel
  have hfast:StrictAtFast (row 19 1) 19 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 1) 19 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 1) 19 1 hvalid hfast

theorem sr19p2:∀ i ∈ List.range 1,StrictCheckAt 19 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 2) 19 2:=by decide +kernel
  have hfast:StrictAtFast (row 19 2) 19 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 2) 19 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 2) 19 2 hvalid hfast

theorem sr19p3:∀ i ∈ List.range 1,StrictCheckAt 19 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 3) 19 3:=by decide +kernel
  have hfast:StrictAtFast (row 19 3) 19 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 3) 19 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 3) 19 3 hvalid hfast

theorem sr19p4:∀ i ∈ List.range 1,StrictCheckAt 19 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 4) 19 4:=by decide +kernel
  have hfast:StrictAtFast (row 19 4) 19 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 4) 19 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 4) 19 4 hvalid hfast

theorem sr19p5:∀ i ∈ List.range 1,StrictCheckAt 19 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 5) 19 5:=by decide +kernel
  have hfast:StrictAtFast (row 19 5) 19 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 5) 19 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 5) 19 5 hvalid hfast

theorem sr19p6:∀ i ∈ List.range 1,StrictCheckAt 19 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 6) 19 6:=by decide +kernel
  have hfast:StrictAtFast (row 19 6) 19 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 6) 19 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 6) 19 6 hvalid hfast

theorem sr19p7:∀ i ∈ List.range 1,StrictCheckAt 19 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 7) 19 7:=by decide +kernel
  have hfast:StrictAtFast (row 19 7) 19 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 7) 19 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 7) 19 7 hvalid hfast

theorem sr19p8:∀ i ∈ List.range 1,StrictCheckAt 19 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 8) 19 8:=by decide +kernel
  have hfast:StrictAtFast (row 19 8) 19 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 8) 19 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 8) 19 8 hvalid hfast

theorem sr19p9:∀ i ∈ List.range 1,StrictCheckAt 19 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 9) 19 9:=by decide +kernel
  have hfast:StrictAtFast (row 19 9) 19 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 9) 19 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 9) 19 9 hvalid hfast

theorem sr19p10:∀ i ∈ List.range 1,StrictCheckAt 19 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 10) 19 10:=by decide +kernel
  have hfast:StrictAtFast (row 19 10) 19 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 10) 19 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 10) 19 10 hvalid hfast

theorem sr19p11:∀ i ∈ List.range 1,StrictCheckAt 19 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 11) 19 11:=by decide +kernel
  have hfast:StrictAtFast (row 19 11) 19 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 11) 19 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 11) 19 11 hvalid hfast

theorem sr19p12:∀ i ∈ List.range 1,StrictCheckAt 19 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 12) 19 12:=by decide +kernel
  have hfast:StrictAtFast (row 19 12) 19 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 12) 19 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 12) 19 12 hvalid hfast

theorem sr19p13:∀ i ∈ List.range 1,StrictCheckAt 19 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 13) 19 13:=by decide +kernel
  have hfast:StrictAtFast (row 19 13) 19 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 13) 19 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 13) 19 13 hvalid hfast

theorem sr19p14:∀ i ∈ List.range 1,StrictCheckAt 19 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 14) 19 14:=by decide +kernel
  have hfast:StrictAtFast (row 19 14) 19 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 14) 19 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 14) 19 14 hvalid hfast

theorem sr19p15:∀ i ∈ List.range 1,StrictCheckAt 19 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 15) 19 15:=by decide +kernel
  have hfast:StrictAtFast (row 19 15) 19 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 15) 19 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 15) 19 15 hvalid hfast

theorem sr19p16:∀ i ∈ List.range 1,StrictCheckAt 19 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 16) 19 16:=by decide +kernel
  have hfast:StrictAtFast (row 19 16) 19 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 16) 19 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 16) 19 16 hvalid hfast

theorem sr19p17:∀ i ∈ List.range 1,StrictCheckAt 19 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 17) 19 17:=by decide +kernel
  have hfast:StrictAtFast (row 19 17) 19 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 17) 19 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 17) 19 17 hvalid hfast

theorem sr19p18:∀ i ∈ List.range 1,StrictCheckAt 19 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 18) 19 18:=by decide +kernel
  have hfast:StrictAtFast (row 19 18) 19 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 18) 19 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 18) 19 18 hvalid hfast

theorem sr19p19:∀ i ∈ List.range 1,StrictCheckAt 19 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 19) 19 19:=by decide +kernel
  have hfast:StrictAtFast (row 19 19) 19 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 19) 19 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 19) 19 19 hvalid hfast

theorem sr19p20:∀ i ∈ List.range 1,StrictCheckAt 19 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 20) 19 20:=by decide +kernel
  have hfast:StrictAtFast (row 19 20) 19 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 20) 19 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 20) 19 20 hvalid hfast

theorem sr19p21:∀ i ∈ List.range 1,StrictCheckAt 19 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 21) 19 21:=by decide +kernel
  have hfast:StrictAtFast (row 19 21) 19 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 21) 19 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 21) 19 21 hvalid hfast

theorem sr19p22:∀ i ∈ List.range 1,StrictCheckAt 19 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 22) 19 22:=by decide +kernel
  have hfast:StrictAtFast (row 19 22) 19 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 22) 19 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 22) 19 22 hvalid hfast

theorem sr19p23:∀ i ∈ List.range 1,StrictCheckAt 19 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 23) 19 23:=by decide +kernel
  have hfast:StrictAtFast (row 19 23) 19 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 23) 19 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 23) 19 23 hvalid hfast

theorem sr19p24:∀ i ∈ List.range 1,StrictCheckAt 19 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 24) 19 24:=by decide +kernel
  have hfast:StrictAtFast (row 19 24) 19 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 24) 19 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 24) 19 24 hvalid hfast

theorem sr19p25:∀ i ∈ List.range 1,StrictCheckAt 19 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 25) 19 25:=by decide +kernel
  have hfast:StrictAtFast (row 19 25) 19 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 25) 19 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 25) 19 25 hvalid hfast

theorem sr19p26:∀ i ∈ List.range 1,StrictCheckAt 19 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 26) 19 26:=by decide +kernel
  have hfast:StrictAtFast (row 19 26) 19 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 26) 19 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 26) 19 26 hvalid hfast

theorem sr19p27:∀ i ∈ List.range 1,StrictCheckAt 19 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 27) 19 27:=by decide +kernel
  have hfast:StrictAtFast (row 19 27) 19 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 27) 19 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 27) 19 27 hvalid hfast

theorem sr19p28:∀ i ∈ List.range 1,StrictCheckAt 19 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 28) 19 28:=by decide +kernel
  have hfast:StrictAtFast (row 19 28) 19 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 28) 19 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 28) 19 28 hvalid hfast

theorem sr19p29:∀ i ∈ List.range 1,StrictCheckAt 19 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 29) 19 29:=by decide +kernel
  have hfast:StrictAtFast (row 19 29) 19 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 29) 19 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 29) 19 29 hvalid hfast

theorem sr19p30:∀ i ∈ List.range 1,StrictCheckAt 19 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 30) 19 30:=by decide +kernel
  have hfast:StrictAtFast (row 19 30) 19 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 30) 19 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 30) 19 30 hvalid hfast

theorem sr19p31:∀ i ∈ List.range 1,StrictCheckAt 19 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 31) 19 31:=by decide +kernel
  have hfast:StrictAtFast (row 19 31) 19 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 31) 19 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 31) 19 31 hvalid hfast

theorem sr19p32:∀ i ∈ List.range 1,StrictCheckAt 19 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 32) 19 32:=by decide +kernel
  have hfast:StrictAtFast (row 19 32) 19 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 32) 19 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 32) 19 32 hvalid hfast

theorem sr19p33:∀ i ∈ List.range 1,StrictCheckAt 19 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 33) 19 33:=by decide +kernel
  have hfast:StrictAtFast (row 19 33) 19 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 33) 19 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 33) 19 33 hvalid hfast

theorem sr19p34:∀ i ∈ List.range 1,StrictCheckAt 19 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 34) 19 34:=by decide +kernel
  have hfast:StrictAtFast (row 19 34) 19 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 34) 19 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 34) 19 34 hvalid hfast

theorem sr19p35:∀ i ∈ List.range 1,StrictCheckAt 19 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 35) 19 35:=by decide +kernel
  have hfast:StrictAtFast (row 19 35) 19 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 35) 19 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 35) 19 35 hvalid hfast

theorem sr19p36:∀ i ∈ List.range 1,StrictCheckAt 19 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 36) 19 36:=by decide +kernel
  have hfast:StrictAtFast (row 19 36) 19 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 36) 19 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 36) 19 36 hvalid hfast

theorem sr19p37:∀ i ∈ List.range 1,StrictCheckAt 19 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 37) 19 37:=by decide +kernel
  have hfast:StrictAtFast (row 19 37) 19 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 37) 19 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 37) 19 37 hvalid hfast

theorem sr19p38:∀ i ∈ List.range 1,StrictCheckAt 19 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 38) 19 38:=by decide +kernel
  have hfast:StrictAtFast (row 19 38) 19 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 38) 19 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 38) 19 38 hvalid hfast

theorem sr19p39:∀ i ∈ List.range 1,StrictCheckAt 19 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 39) 19 39:=by decide +kernel
  have hfast:StrictAtFast (row 19 39) 19 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 39) 19 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 39) 19 39 hvalid hfast

theorem sr19p40:∀ i ∈ List.range 1,StrictCheckAt 19 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 40) 19 40:=by decide +kernel
  have hfast:StrictAtFast (row 19 40) 19 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 40) 19 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 40) 19 40 hvalid hfast

theorem sr19p41:∀ i ∈ List.range 1,StrictCheckAt 19 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 41) 19 41:=by decide +kernel
  have hfast:StrictAtFast (row 19 41) 19 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 41) 19 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 41) 19 41 hvalid hfast

theorem sr19p42:∀ i ∈ List.range 1,StrictCheckAt 19 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 42) 19 42:=by decide +kernel
  have hfast:StrictAtFast (row 19 42) 19 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 42) 19 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 42) 19 42 hvalid hfast

theorem sr19p43:∀ i ∈ List.range 1,StrictCheckAt 19 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 43) 19 43:=by decide +kernel
  have hfast:StrictAtFast (row 19 43) 19 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 43) 19 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 43) 19 43 hvalid hfast

theorem sr19p44:∀ i ∈ List.range 1,StrictCheckAt 19 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 44) 19 44:=by decide +kernel
  have hfast:StrictAtFast (row 19 44) 19 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 44) 19 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 44) 19 44 hvalid hfast

theorem sr19p45:∀ i ∈ List.range 1,StrictCheckAt 19 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 45) 19 45:=by decide +kernel
  have hfast:StrictAtFast (row 19 45) 19 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 45) 19 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 45) 19 45 hvalid hfast

theorem sr19p46:∀ i ∈ List.range 1,StrictCheckAt 19 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 46) 19 46:=by decide +kernel
  have hfast:StrictAtFast (row 19 46) 19 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 46) 19 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 46) 19 46 hvalid hfast

theorem sr19p47:∀ i ∈ List.range 1,StrictCheckAt 19 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 47) 19 47:=by decide +kernel
  have hfast:StrictAtFast (row 19 47) 19 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 47) 19 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 47) 19 47 hvalid hfast

theorem sr19p48:∀ i ∈ List.range 1,StrictCheckAt 19 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 48) 19 48:=by decide +kernel
  have hfast:StrictAtFast (row 19 48) 19 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 48) 19 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 48) 19 48 hvalid hfast

theorem sr19p49:∀ i ∈ List.range 1,StrictCheckAt 19 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 49) 19 49:=by decide +kernel
  have hfast:StrictAtFast (row 19 49) 19 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 49) 19 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 49) 19 49 hvalid hfast

theorem sr19p50:∀ i ∈ List.range 1,StrictCheckAt 19 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 50) 19 50:=by decide +kernel
  have hfast:StrictAtFast (row 19 50) 19 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 50) 19 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 50) 19 50 hvalid hfast

theorem sr19p51:∀ i ∈ List.range 1,StrictCheckAt 19 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 51) 19 51:=by decide +kernel
  have hfast:StrictAtFast (row 19 51) 19 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 51) 19 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 51) 19 51 hvalid hfast

theorem sr19p52:∀ i ∈ List.range 1,StrictCheckAt 19 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 52) 19 52:=by decide +kernel
  have hfast:StrictAtFast (row 19 52) 19 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 52) 19 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 52) 19 52 hvalid hfast

theorem sr19p53:∀ i ∈ List.range 1,StrictCheckAt 19 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 53) 19 53:=by decide +kernel
  have hfast:StrictAtFast (row 19 53) 19 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 53) 19 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 53) 19 53 hvalid hfast

theorem sr19p54:∀ i ∈ List.range 1,StrictCheckAt 19 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 54) 19 54:=by decide +kernel
  have hfast:StrictAtFast (row 19 54) 19 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 54) 19 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 54) 19 54 hvalid hfast

theorem sr19p55:∀ i ∈ List.range 1,StrictCheckAt 19 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 55) 19 55:=by decide +kernel
  have hfast:StrictAtFast (row 19 55) 19 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 55) 19 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 55) 19 55 hvalid hfast

theorem sr19p56:∀ i ∈ List.range 1,StrictCheckAt 19 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 56) 19 56:=by decide +kernel
  have hfast:StrictAtFast (row 19 56) 19 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 56) 19 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 56) 19 56 hvalid hfast

theorem sr19p57:∀ i ∈ List.range 1,StrictCheckAt 19 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 57) 19 57:=by decide +kernel
  have hfast:StrictAtFast (row 19 57) 19 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 57) 19 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 57) 19 57 hvalid hfast

theorem sr19p58:∀ i ∈ List.range 1,StrictCheckAt 19 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 58) 19 58:=by decide +kernel
  have hfast:StrictAtFast (row 19 58) 19 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 58) 19 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 58) 19 58 hvalid hfast

theorem sr19p59:∀ i ∈ List.range 1,StrictCheckAt 19 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 59) 19 59:=by decide +kernel
  have hfast:StrictAtFast (row 19 59) 19 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 59) 19 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 59) 19 59 hvalid hfast

theorem sr19p60:∀ i ∈ List.range 1,StrictCheckAt 19 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 60) 19 60:=by decide +kernel
  have hfast:StrictAtFast (row 19 60) 19 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 60) 19 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 60) 19 60 hvalid hfast

theorem sr19p61:∀ i ∈ List.range 1,StrictCheckAt 19 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 61) 19 61:=by decide +kernel
  have hfast:StrictAtFast (row 19 61) 19 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 61) 19 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 61) 19 61 hvalid hfast

theorem sr19p62:∀ i ∈ List.range 1,StrictCheckAt 19 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 62) 19 62:=by decide +kernel
  have hfast:StrictAtFast (row 19 62) 19 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 62) 19 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 62) 19 62 hvalid hfast

theorem sr19p63:∀ i ∈ List.range 1,StrictCheckAt 19 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 63) 19 63:=by decide +kernel
  have hfast:StrictAtFast (row 19 63) 19 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 63) 19 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 63) 19 63 hvalid hfast

theorem sr19p64:∀ i ∈ List.range 1,StrictCheckAt 19 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 64) 19 64:=by decide +kernel
  have hfast:StrictAtFast (row 19 64) 19 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 64) 19 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 64) 19 64 hvalid hfast

theorem sr19p65:∀ i ∈ List.range 1,StrictCheckAt 19 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 65) 19 65:=by decide +kernel
  have hfast:StrictAtFast (row 19 65) 19 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 65) 19 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 65) 19 65 hvalid hfast

theorem sr19p66:∀ i ∈ List.range 1,StrictCheckAt 19 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 66) 19 66:=by decide +kernel
  have hfast:StrictAtFast (row 19 66) 19 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 66) 19 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 66) 19 66 hvalid hfast

theorem sr19p67:∀ i ∈ List.range 1,StrictCheckAt 19 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 67) 19 67:=by decide +kernel
  have hfast:StrictAtFast (row 19 67) 19 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 67) 19 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 67) 19 67 hvalid hfast

theorem sr19p68:∀ i ∈ List.range 1,StrictCheckAt 19 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 68) 19 68:=by decide +kernel
  have hfast:StrictAtFast (row 19 68) 19 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 68) 19 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 68) 19 68 hvalid hfast

theorem sr19p69:∀ i ∈ List.range 1,StrictCheckAt 19 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 69) 19 69:=by decide +kernel
  have hfast:StrictAtFast (row 19 69) 19 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 69) 19 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 69) 19 69 hvalid hfast

theorem sr19p70:∀ i ∈ List.range 1,StrictCheckAt 19 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 70) 19 70:=by decide +kernel
  have hfast:StrictAtFast (row 19 70) 19 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 70) 19 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 70) 19 70 hvalid hfast

theorem sr19p71:∀ i ∈ List.range 1,StrictCheckAt 19 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 71) 19 71:=by decide +kernel
  have hfast:StrictAtFast (row 19 71) 19 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 71) 19 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 71) 19 71 hvalid hfast

theorem sr19p72:∀ i ∈ List.range 1,StrictCheckAt 19 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 72) 19 72:=by decide +kernel
  have hfast:StrictAtFast (row 19 72) 19 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 72) 19 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 72) 19 72 hvalid hfast

theorem sr19p73:∀ i ∈ List.range 1,StrictCheckAt 19 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 73) 19 73:=by decide +kernel
  have hfast:StrictAtFast (row 19 73) 19 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 73) 19 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 73) 19 73 hvalid hfast

theorem sr19p74:∀ i ∈ List.range 1,StrictCheckAt 19 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 74) 19 74:=by decide +kernel
  have hfast:StrictAtFast (row 19 74) 19 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 74) 19 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 74) 19 74 hvalid hfast

theorem sr19p75:∀ i ∈ List.range 1,StrictCheckAt 19 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 75) 19 75:=by decide +kernel
  have hfast:StrictAtFast (row 19 75) 19 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 75) 19 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 75) 19 75 hvalid hfast

theorem sr19p76:∀ i ∈ List.range 1,StrictCheckAt 19 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 76) 19 76:=by decide +kernel
  have hfast:StrictAtFast (row 19 76) 19 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 76) 19 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 76) 19 76 hvalid hfast

theorem sr19p77:∀ i ∈ List.range 1,StrictCheckAt 19 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 77) 19 77:=by decide +kernel
  have hfast:StrictAtFast (row 19 77) 19 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 77) 19 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 77) 19 77 hvalid hfast

theorem sr19p78:∀ i ∈ List.range 1,StrictCheckAt 19 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 78) 19 78:=by decide +kernel
  have hfast:StrictAtFast (row 19 78) 19 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 78) 19 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 78) 19 78 hvalid hfast

theorem sr19p79:∀ i ∈ List.range 1,StrictCheckAt 19 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 79) 19 79:=by decide +kernel
  have hfast:StrictAtFast (row 19 79) 19 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 79) 19 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 79) 19 79 hvalid hfast

theorem sr19p80:∀ i ∈ List.range 1,StrictCheckAt 19 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 80) 19 80:=by decide +kernel
  have hfast:StrictAtFast (row 19 80) 19 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 80) 19 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 80) 19 80 hvalid hfast

theorem sr19p81:∀ i ∈ List.range 1,StrictCheckAt 19 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 81) 19 81:=by decide +kernel
  have hfast:StrictAtFast (row 19 81) 19 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 81) 19 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 81) 19 81 hvalid hfast

theorem sr19p82:∀ i ∈ List.range 1,StrictCheckAt 19 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 82) 19 82:=by decide +kernel
  have hfast:StrictAtFast (row 19 82) 19 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 82) 19 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 82) 19 82 hvalid hfast

theorem sr19p83:∀ i ∈ List.range 1,StrictCheckAt 19 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 83) 19 83:=by decide +kernel
  have hfast:StrictAtFast (row 19 83) 19 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 83) 19 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 83) 19 83 hvalid hfast

theorem sr19p84:∀ i ∈ List.range 1,StrictCheckAt 19 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 84) 19 84:=by decide +kernel
  have hfast:StrictAtFast (row 19 84) 19 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 84) 19 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 84) 19 84 hvalid hfast

theorem sr19p85:∀ i ∈ List.range 1,StrictCheckAt 19 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 85) 19 85:=by decide +kernel
  have hfast:StrictAtFast (row 19 85) 19 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 85) 19 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 85) 19 85 hvalid hfast

theorem sr19p86:∀ i ∈ List.range 1,StrictCheckAt 19 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 86) 19 86:=by decide +kernel
  have hfast:StrictAtFast (row 19 86) 19 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 86) 19 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 86) 19 86 hvalid hfast

theorem sr19p87:∀ i ∈ List.range 1,StrictCheckAt 19 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 87) 19 87:=by decide +kernel
  have hfast:StrictAtFast (row 19 87) 19 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 87) 19 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 87) 19 87 hvalid hfast

theorem sr19p88:∀ i ∈ List.range 1,StrictCheckAt 19 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 88) 19 88:=by decide +kernel
  have hfast:StrictAtFast (row 19 88) 19 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 88) 19 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 88) 19 88 hvalid hfast

theorem sr19p89:∀ i ∈ List.range 1,StrictCheckAt 19 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 89) 19 89:=by decide +kernel
  have hfast:StrictAtFast (row 19 89) 19 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 89) 19 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 89) 19 89 hvalid hfast

theorem sr19p90:∀ i ∈ List.range 1,StrictCheckAt 19 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 90) 19 90:=by decide +kernel
  have hfast:StrictAtFast (row 19 90) 19 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 90) 19 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 90) 19 90 hvalid hfast

theorem sr19p91:∀ i ∈ List.range 1,StrictCheckAt 19 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 91) 19 91:=by decide +kernel
  have hfast:StrictAtFast (row 19 91) 19 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 91) 19 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 91) 19 91 hvalid hfast

theorem sr19p92:∀ i ∈ List.range 1,StrictCheckAt 19 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 92) 19 92:=by decide +kernel
  have hfast:StrictAtFast (row 19 92) 19 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 92) 19 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 92) 19 92 hvalid hfast

theorem sr19p93:∀ i ∈ List.range 1,StrictCheckAt 19 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 93) 19 93:=by decide +kernel
  have hfast:StrictAtFast (row 19 93) 19 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 93) 19 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 93) 19 93 hvalid hfast

theorem sr19p94:∀ i ∈ List.range 1,StrictCheckAt 19 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 94) 19 94:=by decide +kernel
  have hfast:StrictAtFast (row 19 94) 19 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 94) 19 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 94) 19 94 hvalid hfast

theorem sr19p95:∀ i ∈ List.range 1,StrictCheckAt 19 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 95) 19 95:=by decide +kernel
  have hfast:StrictAtFast (row 19 95) 19 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 95) 19 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 95) 19 95 hvalid hfast

theorem sr19p96:∀ i ∈ List.range 1,StrictCheckAt 19 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 96) 19 96:=by decide +kernel
  have hfast:StrictAtFast (row 19 96) 19 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 96) 19 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 96) 19 96 hvalid hfast

theorem sr19p97:∀ i ∈ List.range 1,StrictCheckAt 19 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 97) 19 97:=by decide +kernel
  have hfast:StrictAtFast (row 19 97) 19 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 97) 19 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 97) 19 97 hvalid hfast

theorem sr19p98:∀ i ∈ List.range 1,StrictCheckAt 19 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 98) 19 98:=by decide +kernel
  have hfast:StrictAtFast (row 19 98) 19 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 98) 19 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 98) 19 98 hvalid hfast

theorem sr19p99:∀ i ∈ List.range 1,StrictCheckAt 19 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 99) 19 99:=by decide +kernel
  have hfast:StrictAtFast (row 19 99) 19 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 99) 19 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 99) 19 99 hvalid hfast

theorem sr19p100:∀ i ∈ List.range 1,StrictCheckAt 19 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 100) 19 100:=by decide +kernel
  have hfast:StrictAtFast (row 19 100) 19 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 100) 19 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 100) 19 100 hvalid hfast

theorem sr19p101:∀ i ∈ List.range 1,StrictCheckAt 19 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 101) 19 101:=by decide +kernel
  have hfast:StrictAtFast (row 19 101) 19 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 101) 19 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 101) 19 101 hvalid hfast

theorem sr19p102:∀ i ∈ List.range 1,StrictCheckAt 19 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 102) 19 102:=by decide +kernel
  have hfast:StrictAtFast (row 19 102) 19 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 102) 19 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 102) 19 102 hvalid hfast

theorem sr19p103:∀ i ∈ List.range 1,StrictCheckAt 19 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 103) 19 103:=by decide +kernel
  have hfast:StrictAtFast (row 19 103) 19 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 103) 19 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 103) 19 103 hvalid hfast

theorem sr19p104:∀ i ∈ List.range 1,StrictCheckAt 19 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 104) 19 104:=by decide +kernel
  have hfast:StrictAtFast (row 19 104) 19 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 104) 19 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 104) 19 104 hvalid hfast

theorem sr19p105:∀ i ∈ List.range 1,StrictCheckAt 19 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 105) 19 105:=by decide +kernel
  have hfast:StrictAtFast (row 19 105) 19 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 105) 19 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 105) 19 105 hvalid hfast

theorem sr19p106:∀ i ∈ List.range 1,StrictCheckAt 19 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 106) 19 106:=by decide +kernel
  have hfast:StrictAtFast (row 19 106) 19 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 106) 19 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 106) 19 106 hvalid hfast

theorem sr19p107:∀ i ∈ List.range 1,StrictCheckAt 19 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 107) 19 107:=by decide +kernel
  have hfast:StrictAtFast (row 19 107) 19 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 107) 19 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 107) 19 107 hvalid hfast

theorem sr19p108:∀ i ∈ List.range 1,StrictCheckAt 19 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 108) 19 108:=by decide +kernel
  have hfast:StrictAtFast (row 19 108) 19 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 108) 19 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 108) 19 108 hvalid hfast

theorem sr19p109:∀ i ∈ List.range 1,StrictCheckAt 19 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 109) 19 109:=by decide +kernel
  have hfast:StrictAtFast (row 19 109) 19 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 109) 19 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 109) 19 109 hvalid hfast

theorem sr19p110:∀ i ∈ List.range 1,StrictCheckAt 19 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 110) 19 110:=by decide +kernel
  have hfast:StrictAtFast (row 19 110) 19 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 110) 19 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 110) 19 110 hvalid hfast

theorem sr19p111:∀ i ∈ List.range 1,StrictCheckAt 19 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 111) 19 111:=by decide +kernel
  have hfast:StrictAtFast (row 19 111) 19 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 111) 19 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 111) 19 111 hvalid hfast

theorem sr19p112:∀ i ∈ List.range 1,StrictCheckAt 19 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 112) 19 112:=by decide +kernel
  have hfast:StrictAtFast (row 19 112) 19 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 112) 19 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 112) 19 112 hvalid hfast

theorem sr19p113:∀ i ∈ List.range 1,StrictCheckAt 19 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 113) 19 113:=by decide +kernel
  have hfast:StrictAtFast (row 19 113) 19 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 113) 19 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 113) 19 113 hvalid hfast

theorem sr19p114:∀ i ∈ List.range 1,StrictCheckAt 19 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 114) 19 114:=by decide +kernel
  have hfast:StrictAtFast (row 19 114) 19 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 114) 19 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 114) 19 114 hvalid hfast

theorem sr19p115:∀ i ∈ List.range 1,StrictCheckAt 19 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 115) 19 115:=by decide +kernel
  have hfast:StrictAtFast (row 19 115) 19 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 115) 19 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 115) 19 115 hvalid hfast

theorem sr19p116:∀ i ∈ List.range 1,StrictCheckAt 19 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 116) 19 116:=by decide +kernel
  have hfast:StrictAtFast (row 19 116) 19 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 116) 19 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 116) 19 116 hvalid hfast

theorem sr19p117:∀ i ∈ List.range 1,StrictCheckAt 19 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 117) 19 117:=by decide +kernel
  have hfast:StrictAtFast (row 19 117) 19 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 117) 19 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 117) 19 117 hvalid hfast

theorem sr19p118:∀ i ∈ List.range 1,StrictCheckAt 19 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 118) 19 118:=by decide +kernel
  have hfast:StrictAtFast (row 19 118) 19 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 118) 19 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 118) 19 118 hvalid hfast

theorem sr19p119:∀ i ∈ List.range 1,StrictCheckAt 19 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 119) 19 119:=by decide +kernel
  have hfast:StrictAtFast (row 19 119) 19 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 119) 19 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 119) 19 119 hvalid hfast

theorem sr19p120:∀ i ∈ List.range 1,StrictCheckAt 19 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 120) 19 120:=by decide +kernel
  have hfast:StrictAtFast (row 19 120) 19 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 120) 19 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 120) 19 120 hvalid hfast

theorem sr19p121:∀ i ∈ List.range 1,StrictCheckAt 19 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 121) 19 121:=by decide +kernel
  have hfast:StrictAtFast (row 19 121) 19 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 121) 19 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 121) 19 121 hvalid hfast

theorem sr19p122:∀ i ∈ List.range 1,StrictCheckAt 19 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 122) 19 122:=by decide +kernel
  have hfast:StrictAtFast (row 19 122) 19 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 122) 19 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 122) 19 122 hvalid hfast

theorem sr19p123:∀ i ∈ List.range 1,StrictCheckAt 19 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 123) 19 123:=by decide +kernel
  have hfast:StrictAtFast (row 19 123) 19 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 123) 19 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 123) 19 123 hvalid hfast

theorem br19p0:∀ i ∈ List.range 4,BaseCheckAt 19 (0+i):=by decide +kernel

theorem br19p1:∀ i ∈ List.range 4,BaseCheckAt 19 (4+i):=by decide +kernel

theorem br19p2:∀ i ∈ List.range 4,BaseCheckAt 19 (8+i):=by decide +kernel

theorem br19p3:∀ i ∈ List.range 4,BaseCheckAt 19 (12+i):=by decide +kernel

theorem br19p4:∀ i ∈ List.range 4,BaseCheckAt 19 (16+i):=by decide +kernel

theorem br19p5:∀ i ∈ List.range 4,BaseCheckAt 19 (20+i):=by decide +kernel

theorem br19p6:∀ i ∈ List.range 4,BaseCheckAt 19 (24+i):=by decide +kernel

theorem br19p7:∀ i ∈ List.range 4,BaseCheckAt 19 (28+i):=by decide +kernel

theorem br19p8:∀ i ∈ List.range 4,BaseCheckAt 19 (32+i):=by decide +kernel

theorem br19p9:∀ i ∈ List.range 4,BaseCheckAt 19 (36+i):=by decide +kernel

theorem br19p10:∀ i ∈ List.range 4,BaseCheckAt 19 (40+i):=by decide +kernel

theorem br19p11:∀ i ∈ List.range 4,BaseCheckAt 19 (44+i):=by decide +kernel

theorem br19p12:∀ i ∈ List.range 4,BaseCheckAt 19 (48+i):=by decide +kernel

theorem br19p13:∀ i ∈ List.range 4,BaseCheckAt 19 (52+i):=by decide +kernel

theorem br19p14:∀ i ∈ List.range 4,BaseCheckAt 19 (56+i):=by decide +kernel

theorem br19p15:∀ i ∈ List.range 4,BaseCheckAt 19 (60+i):=by decide +kernel



theorem br19p16:∀ i ∈ List.range 4,BaseCheckAt 19 (64+i):=by decide +kernel

theorem br19p17:∀ i ∈ List.range 4,BaseCheckAt 19 (68+i):=by decide +kernel

theorem br19p18:∀ i ∈ List.range 4,BaseCheckAt 19 (72+i):=by decide +kernel

theorem br19p19:∀ i ∈ List.range 4,BaseCheckAt 19 (76+i):=by decide +kernel

theorem br19p20:∀ i ∈ List.range 4,BaseCheckAt 19 (80+i):=by decide +kernel

theorem br19p21:∀ i ∈ List.range 4,BaseCheckAt 19 (84+i):=by decide +kernel

theorem br19p22:∀ i ∈ List.range 4,BaseCheckAt 19 (88+i):=by decide +kernel

theorem br19p23:∀ i ∈ List.range 4,BaseCheckAt 19 (92+i):=by decide +kernel

theorem br19p24:∀ i ∈ List.range 4,BaseCheckAt 19 (96+i):=by decide +kernel

theorem br19p25:∀ i ∈ List.range 4,BaseCheckAt 19 (100+i):=by decide +kernel

theorem br19p26:∀ i ∈ List.range 4,BaseCheckAt 19 (104+i):=by decide +kernel

theorem br19p27:∀ i ∈ List.range 4,BaseCheckAt 19 (108+i):=by decide +kernel

theorem br19p28:∀ i ∈ List.range 4,BaseCheckAt 19 (112+i):=by decide +kernel

theorem br19p29:∀ i ∈ List.range 4,BaseCheckAt 19 (116+i):=by decide +kernel

theorem br19p30:∀ i ∈ List.range 4,BaseCheckAt 19 (120+i):=by decide +kernel



theorem cr19:∀ V ∈ List.range 124,CorrectAt 19 V:=by
  intro V hV
  have hv:V < 124:=List.mem_range.mp hV
  by_cases h0_16:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr19p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr19p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr19p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr19p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr19p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr19p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr19p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr19p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_16:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr19p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr19p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr19p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr19p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_16:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr19p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr19p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_16:V < 120
        · have h:=cr19p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · have h:=cr19p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem zr19:∀ V ∈ List.range 124,ZeroCheckAt 19 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 19 V (by omega) (by omega) (by omega)
theorem sr19:∀ V ∈ List.range 124,StrictCheckAt 19 V:=by
  intro V hV
  have hv:V < 124:=List.mem_range.mp hV
  by_cases h0_124:V < 62
  · by_cases h0_62:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr19p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr19p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr19p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr19p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr19p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr19p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr19p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr19p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr19p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr19p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr19p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr19p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr19p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr19p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr19p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have h:=sr19p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr19p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
            · by_cases h17_19:V < 18
              · have h:=sr19p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr19p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have h:=sr19p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr19p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
            · by_cases h21_23:V < 22
              · have h:=sr19p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr19p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have h:=sr19p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr19p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
            · by_cases h25_27:V < 26
              · have h:=sr19p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr19p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have h:=sr19p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr19p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr19p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr19p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
    · by_cases h31_62:V < 46
      · by_cases h31_46:V < 38
        · by_cases h31_38:V < 34
          · by_cases h31_34:V < 32
            · have h:=sr19p31 (V-31) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
            · by_cases h32_34:V < 33
              · have h:=sr19p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr19p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
          · by_cases h34_38:V < 36
            · by_cases h34_36:V < 35
              · have h:=sr19p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr19p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
            · by_cases h36_38:V < 37
              · have h:=sr19p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr19p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
        · by_cases h38_46:V < 42
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have h:=sr19p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr19p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
            · by_cases h40_42:V < 41
              · have h:=sr19p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr19p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
          · by_cases h42_46:V < 44
            · by_cases h42_44:V < 43
              · have h:=sr19p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr19p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
            · by_cases h44_46:V < 45
              · have h:=sr19p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr19p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
      · by_cases h46_62:V < 54
        · by_cases h46_54:V < 50
          · by_cases h46_50:V < 48
            · by_cases h46_48:V < 47
              · have h:=sr19p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr19p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
            · by_cases h48_50:V < 49
              · have h:=sr19p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr19p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have h:=sr19p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr19p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
            · by_cases h52_54:V < 53
              · have h:=sr19p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr19p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
        · by_cases h54_62:V < 58
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have h:=sr19p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr19p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
            · by_cases h56_58:V < 57
              · have h:=sr19p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr19p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
          · by_cases h58_62:V < 60
            · by_cases h58_60:V < 59
              · have h:=sr19p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr19p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
            · by_cases h60_62:V < 61
              · have h:=sr19p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr19p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
  · by_cases h62_124:V < 93
    · by_cases h62_93:V < 77
      · by_cases h62_77:V < 69
        · by_cases h62_69:V < 65
          · by_cases h62_65:V < 63
            · have h:=sr19p62 (V-62) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
            · by_cases h63_65:V < 64
              · have h:=sr19p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr19p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · by_cases h65_69:V < 67
            · by_cases h65_67:V < 66
              · have h:=sr19p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr19p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
            · by_cases h67_69:V < 68
              · have h:=sr19p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr19p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h69_77:V < 73
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have h:=sr19p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr19p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
            · by_cases h71_73:V < 72
              · have h:=sr19p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr19p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have h:=sr19p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr19p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
            · by_cases h75_77:V < 76
              · have h:=sr19p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr19p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h77_93:V < 85
        · by_cases h77_85:V < 81
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have h:=sr19p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr19p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
            · by_cases h79_81:V < 80
              · have h:=sr19p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr19p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have h:=sr19p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr19p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
            · by_cases h83_85:V < 84
              · have h:=sr19p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr19p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h85_93:V < 89
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have h:=sr19p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr19p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
            · by_cases h87_89:V < 88
              · have h:=sr19p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr19p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have h:=sr19p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr19p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr19p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr19p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h93_124:V < 108
      · by_cases h93_108:V < 100
        · by_cases h93_100:V < 96
          · by_cases h93_96:V < 94
            · have h:=sr19p93 (V-93) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
            · by_cases h94_96:V < 95
              · have h:=sr19p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr19p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have h:=sr19p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr19p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
            · by_cases h98_100:V < 99
              · have h:=sr19p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr19p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
        · by_cases h100_108:V < 104
          · by_cases h100_104:V < 102
            · by_cases h100_102:V < 101
              · have h:=sr19p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr19p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
            · by_cases h102_104:V < 103
              · have h:=sr19p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr19p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
          · by_cases h104_108:V < 106
            · by_cases h104_106:V < 105
              · have h:=sr19p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr19p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
            · by_cases h106_108:V < 107
              · have h:=sr19p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr19p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
      · by_cases h108_124:V < 116
        · by_cases h108_116:V < 112
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have h:=sr19p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr19p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
            · by_cases h110_112:V < 111
              · have h:=sr19p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr19p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have h:=sr19p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr19p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
            · by_cases h114_116:V < 115
              · have h:=sr19p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr19p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
        · by_cases h116_124:V < 120
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have h:=sr19p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr19p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
            · by_cases h118_120:V < 119
              · have h:=sr19p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr19p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
          · by_cases h120_124:V < 122
            · by_cases h120_122:V < 121
              · have h:=sr19p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
              · have h:=sr19p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
            · by_cases h122_124:V < 123
              · have h:=sr19p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
              · have h:=sr19p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h

theorem br19:∀ V ∈ List.range 124,BaseCheckAt 19 V:=by
  intro V hV
  have hv:V < 124:=List.mem_range.mp hV
  by_cases h0_31:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br19p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br19p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br19p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br19p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br19p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br19p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br19p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br19p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br19p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br19p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br19p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br19p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br19p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br19p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br19p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_31:V < 92
    · by_cases h15_23:V < 76
      · by_cases h15_19:V < 68
        · by_cases h15_17:V < 64
          · have h:=br19p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br19p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · by_cases h17_19:V < 72
          · have h:=br19p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br19p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h19_23:V < 84
        · by_cases h19_21:V < 80
          · have h:=br19p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br19p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · by_cases h21_23:V < 88
          · have h:=br19p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br19p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h23_31:V < 108
      · by_cases h23_27:V < 100
        · by_cases h23_25:V < 96
          · have h:=br19p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br19p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · by_cases h25_27:V < 104
          · have h:=br19p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br19p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h27_31:V < 116
        · by_cases h27_29:V < 112
          · have h:=br19p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br19p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h29_31:V < 120
          · have h:=br19p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · have h:=br19p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
