import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr13p0:∀ i ∈ List.range 8,CorrectAt 13 (0+i):=by decide +kernel

theorem cr13p1:∀ i ∈ List.range 8,CorrectAt 13 (8+i):=by decide +kernel

theorem cr13p2:∀ i ∈ List.range 8,CorrectAt 13 (16+i):=by decide +kernel

theorem cr13p3:∀ i ∈ List.range 8,CorrectAt 13 (24+i):=by decide +kernel

theorem cr13p4:∀ i ∈ List.range 8,CorrectAt 13 (32+i):=by decide +kernel

theorem cr13p5:∀ i ∈ List.range 8,CorrectAt 13 (40+i):=by decide +kernel

theorem cr13p6:∀ i ∈ List.range 8,CorrectAt 13 (48+i):=by decide +kernel

theorem cr13p7:∀ i ∈ List.range 8,CorrectAt 13 (56+i):=by decide +kernel

theorem cr13p8:∀ i ∈ List.range 8,CorrectAt 13 (64+i):=by decide +kernel

theorem cr13p9:∀ i ∈ List.range 8,CorrectAt 13 (72+i):=by decide +kernel

theorem cr13p10:∀ i ∈ List.range 8,CorrectAt 13 (80+i):=by decide +kernel

theorem cr13p11:∀ i ∈ List.range 8,CorrectAt 13 (88+i):=by decide +kernel

theorem cr13p12:∀ i ∈ List.range 8,CorrectAt 13 (96+i):=by decide +kernel

theorem cr13p13:∀ i ∈ List.range 8,CorrectAt 13 (104+i):=by decide +kernel

theorem cr13p14:∀ i ∈ List.range 8,CorrectAt 13 (112+i):=by decide +kernel

theorem cr13p15:∀ i ∈ List.range 8,CorrectAt 13 (120+i):=by decide +kernel

theorem cr13p16:∀ i ∈ List.range 2,CorrectAt 13 (128+i):=by decide +kernel

theorem sr13p0:∀ i ∈ List.range 1,StrictCheckAt 13 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 0) 13 0:=by decide +kernel
  have hfast:StrictAtFast (row 13 0) 13 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 0) 13 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 0) 13 0 hvalid hfast

theorem sr13p1:∀ i ∈ List.range 1,StrictCheckAt 13 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 1) 13 1:=by decide +kernel
  have hfast:StrictAtFast (row 13 1) 13 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 1) 13 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 1) 13 1 hvalid hfast

theorem sr13p2:∀ i ∈ List.range 1,StrictCheckAt 13 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 2) 13 2:=by decide +kernel
  have hfast:StrictAtFast (row 13 2) 13 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 2) 13 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 2) 13 2 hvalid hfast

theorem sr13p3:∀ i ∈ List.range 1,StrictCheckAt 13 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 3) 13 3:=by decide +kernel
  have hfast:StrictAtFast (row 13 3) 13 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 3) 13 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 3) 13 3 hvalid hfast

theorem sr13p4:∀ i ∈ List.range 1,StrictCheckAt 13 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 4) 13 4:=by decide +kernel
  have hfast:StrictAtFast (row 13 4) 13 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 4) 13 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 4) 13 4 hvalid hfast

theorem sr13p5:∀ i ∈ List.range 1,StrictCheckAt 13 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 5) 13 5:=by decide +kernel
  have hfast:StrictAtFast (row 13 5) 13 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 5) 13 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 5) 13 5 hvalid hfast

theorem sr13p6:∀ i ∈ List.range 1,StrictCheckAt 13 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 6) 13 6:=by decide +kernel
  have hfast:StrictAtFast (row 13 6) 13 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 6) 13 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 6) 13 6 hvalid hfast

theorem sr13p7:∀ i ∈ List.range 1,StrictCheckAt 13 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 7) 13 7:=by decide +kernel
  have hfast:StrictAtFast (row 13 7) 13 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 7) 13 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 7) 13 7 hvalid hfast

theorem sr13p8:∀ i ∈ List.range 1,StrictCheckAt 13 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 8) 13 8:=by decide +kernel
  have hfast:StrictAtFast (row 13 8) 13 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 8) 13 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 8) 13 8 hvalid hfast

theorem sr13p9:∀ i ∈ List.range 1,StrictCheckAt 13 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 9) 13 9:=by decide +kernel
  have hfast:StrictAtFast (row 13 9) 13 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 9) 13 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 9) 13 9 hvalid hfast

theorem sr13p10:∀ i ∈ List.range 1,StrictCheckAt 13 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 10) 13 10:=by decide +kernel
  have hfast:StrictAtFast (row 13 10) 13 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 10) 13 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 10) 13 10 hvalid hfast

theorem sr13p11:∀ i ∈ List.range 1,StrictCheckAt 13 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 11) 13 11:=by decide +kernel
  have hfast:StrictAtFast (row 13 11) 13 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 11) 13 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 11) 13 11 hvalid hfast

theorem sr13p12:∀ i ∈ List.range 1,StrictCheckAt 13 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 12) 13 12:=by decide +kernel
  have hfast:StrictAtFast (row 13 12) 13 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 12) 13 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 12) 13 12 hvalid hfast

theorem sr13p13:∀ i ∈ List.range 1,StrictCheckAt 13 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 13) 13 13:=by decide +kernel
  have hfast:StrictAtFast (row 13 13) 13 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 13) 13 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 13) 13 13 hvalid hfast

theorem sr13p14:∀ i ∈ List.range 1,StrictCheckAt 13 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 14) 13 14:=by decide +kernel
  have hfast:StrictAtFast (row 13 14) 13 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 14) 13 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 14) 13 14 hvalid hfast

theorem sr13p15:∀ i ∈ List.range 1,StrictCheckAt 13 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 15) 13 15:=by decide +kernel
  have hfast:StrictAtFast (row 13 15) 13 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 15) 13 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 15) 13 15 hvalid hfast

theorem sr13p16:∀ i ∈ List.range 1,StrictCheckAt 13 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 16) 13 16:=by decide +kernel
  have hfast:StrictAtFast (row 13 16) 13 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 16) 13 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 16) 13 16 hvalid hfast

theorem sr13p17:∀ i ∈ List.range 1,StrictCheckAt 13 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 17) 13 17:=by decide +kernel
  have hfast:StrictAtFast (row 13 17) 13 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 17) 13 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 17) 13 17 hvalid hfast

theorem sr13p18:∀ i ∈ List.range 1,StrictCheckAt 13 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 18) 13 18:=by decide +kernel
  have hfast:StrictAtFast (row 13 18) 13 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 18) 13 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 18) 13 18 hvalid hfast

theorem sr13p19:∀ i ∈ List.range 1,StrictCheckAt 13 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 19) 13 19:=by decide +kernel
  have hfast:StrictAtFast (row 13 19) 13 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 19) 13 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 19) 13 19 hvalid hfast

theorem sr13p20:∀ i ∈ List.range 1,StrictCheckAt 13 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 20) 13 20:=by decide +kernel
  have hfast:StrictAtFast (row 13 20) 13 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 20) 13 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 20) 13 20 hvalid hfast

theorem sr13p21:∀ i ∈ List.range 1,StrictCheckAt 13 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 21) 13 21:=by decide +kernel
  have hfast:StrictAtFast (row 13 21) 13 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 21) 13 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 21) 13 21 hvalid hfast

theorem sr13p22:∀ i ∈ List.range 1,StrictCheckAt 13 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 22) 13 22:=by decide +kernel
  have hfast:StrictAtFast (row 13 22) 13 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 22) 13 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 22) 13 22 hvalid hfast

theorem sr13p23:∀ i ∈ List.range 1,StrictCheckAt 13 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 23) 13 23:=by decide +kernel
  have hfast:StrictAtFast (row 13 23) 13 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 23) 13 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 23) 13 23 hvalid hfast

theorem sr13p24:∀ i ∈ List.range 1,StrictCheckAt 13 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 24) 13 24:=by decide +kernel
  have hfast:StrictAtFast (row 13 24) 13 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 24) 13 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 24) 13 24 hvalid hfast

theorem sr13p25:∀ i ∈ List.range 1,StrictCheckAt 13 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 25) 13 25:=by decide +kernel
  have hfast:StrictAtFast (row 13 25) 13 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 25) 13 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 25) 13 25 hvalid hfast

theorem sr13p26:∀ i ∈ List.range 1,StrictCheckAt 13 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 26) 13 26:=by decide +kernel
  have hfast:StrictAtFast (row 13 26) 13 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 26) 13 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 26) 13 26 hvalid hfast

theorem sr13p27:∀ i ∈ List.range 1,StrictCheckAt 13 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 27) 13 27:=by decide +kernel
  have hfast:StrictAtFast (row 13 27) 13 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 27) 13 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 27) 13 27 hvalid hfast

theorem sr13p28:∀ i ∈ List.range 1,StrictCheckAt 13 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 28) 13 28:=by decide +kernel
  have hfast:StrictAtFast (row 13 28) 13 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 28) 13 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 28) 13 28 hvalid hfast

theorem sr13p29:∀ i ∈ List.range 1,StrictCheckAt 13 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 29) 13 29:=by decide +kernel
  have hfast:StrictAtFast (row 13 29) 13 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 29) 13 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 29) 13 29 hvalid hfast

theorem sr13p30:∀ i ∈ List.range 1,StrictCheckAt 13 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 30) 13 30:=by decide +kernel
  have hfast:StrictAtFast (row 13 30) 13 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 30) 13 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 30) 13 30 hvalid hfast

theorem sr13p31:∀ i ∈ List.range 1,StrictCheckAt 13 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 31) 13 31:=by decide +kernel
  have hfast:StrictAtFast (row 13 31) 13 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 31) 13 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 31) 13 31 hvalid hfast

theorem sr13p32:∀ i ∈ List.range 1,StrictCheckAt 13 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 32) 13 32:=by decide +kernel
  have hfast:StrictAtFast (row 13 32) 13 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 32) 13 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 32) 13 32 hvalid hfast

theorem sr13p33:∀ i ∈ List.range 1,StrictCheckAt 13 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 33) 13 33:=by decide +kernel
  have hfast:StrictAtFast (row 13 33) 13 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 33) 13 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 33) 13 33 hvalid hfast

theorem sr13p34:∀ i ∈ List.range 1,StrictCheckAt 13 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 34) 13 34:=by decide +kernel
  have hfast:StrictAtFast (row 13 34) 13 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 34) 13 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 34) 13 34 hvalid hfast

theorem sr13p35:∀ i ∈ List.range 1,StrictCheckAt 13 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 35) 13 35:=by decide +kernel
  have hfast:StrictAtFast (row 13 35) 13 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 35) 13 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 35) 13 35 hvalid hfast

theorem sr13p36:∀ i ∈ List.range 1,StrictCheckAt 13 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 36) 13 36:=by decide +kernel
  have hfast:StrictAtFast (row 13 36) 13 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 36) 13 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 36) 13 36 hvalid hfast

theorem sr13p37:∀ i ∈ List.range 1,StrictCheckAt 13 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 37) 13 37:=by decide +kernel
  have hfast:StrictAtFast (row 13 37) 13 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 37) 13 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 37) 13 37 hvalid hfast

theorem sr13p38:∀ i ∈ List.range 1,StrictCheckAt 13 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 38) 13 38:=by decide +kernel
  have hfast:StrictAtFast (row 13 38) 13 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 38) 13 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 38) 13 38 hvalid hfast

theorem sr13p39:∀ i ∈ List.range 1,StrictCheckAt 13 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 39) 13 39:=by decide +kernel
  have hfast:StrictAtFast (row 13 39) 13 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 39) 13 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 39) 13 39 hvalid hfast

theorem sr13p40:∀ i ∈ List.range 1,StrictCheckAt 13 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 40) 13 40:=by decide +kernel
  have hfast:StrictAtFast (row 13 40) 13 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 40) 13 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 40) 13 40 hvalid hfast

theorem sr13p41:∀ i ∈ List.range 1,StrictCheckAt 13 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 41) 13 41:=by decide +kernel
  have hfast:StrictAtFast (row 13 41) 13 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 41) 13 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 41) 13 41 hvalid hfast

theorem sr13p42:∀ i ∈ List.range 1,StrictCheckAt 13 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 42) 13 42:=by decide +kernel
  have hfast:StrictAtFast (row 13 42) 13 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 42) 13 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 42) 13 42 hvalid hfast

theorem sr13p43:∀ i ∈ List.range 1,StrictCheckAt 13 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 43) 13 43:=by decide +kernel
  have hfast:StrictAtFast (row 13 43) 13 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 43) 13 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 43) 13 43 hvalid hfast

theorem sr13p44:∀ i ∈ List.range 1,StrictCheckAt 13 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 44) 13 44:=by decide +kernel
  have hfast:StrictAtFast (row 13 44) 13 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 44) 13 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 44) 13 44 hvalid hfast

theorem sr13p45:∀ i ∈ List.range 1,StrictCheckAt 13 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 45) 13 45:=by decide +kernel
  have hfast:StrictAtFast (row 13 45) 13 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 45) 13 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 45) 13 45 hvalid hfast

theorem sr13p46:∀ i ∈ List.range 1,StrictCheckAt 13 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 46) 13 46:=by decide +kernel
  have hfast:StrictAtFast (row 13 46) 13 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 46) 13 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 46) 13 46 hvalid hfast

theorem sr13p47:∀ i ∈ List.range 1,StrictCheckAt 13 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 47) 13 47:=by decide +kernel
  have hfast:StrictAtFast (row 13 47) 13 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 47) 13 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 47) 13 47 hvalid hfast

theorem sr13p48:∀ i ∈ List.range 1,StrictCheckAt 13 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 48) 13 48:=by decide +kernel
  have hfast:StrictAtFast (row 13 48) 13 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 48) 13 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 48) 13 48 hvalid hfast

theorem sr13p49:∀ i ∈ List.range 1,StrictCheckAt 13 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 49) 13 49:=by decide +kernel
  have hfast:StrictAtFast (row 13 49) 13 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 49) 13 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 49) 13 49 hvalid hfast

theorem sr13p50:∀ i ∈ List.range 1,StrictCheckAt 13 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 50) 13 50:=by decide +kernel
  have hfast:StrictAtFast (row 13 50) 13 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 50) 13 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 50) 13 50 hvalid hfast

theorem sr13p51:∀ i ∈ List.range 1,StrictCheckAt 13 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 51) 13 51:=by decide +kernel
  have hfast:StrictAtFast (row 13 51) 13 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 51) 13 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 51) 13 51 hvalid hfast

theorem sr13p52:∀ i ∈ List.range 1,StrictCheckAt 13 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 52) 13 52:=by decide +kernel
  have hfast:StrictAtFast (row 13 52) 13 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 52) 13 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 52) 13 52 hvalid hfast

theorem sr13p53:∀ i ∈ List.range 1,StrictCheckAt 13 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 53) 13 53:=by decide +kernel
  have hfast:StrictAtFast (row 13 53) 13 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 53) 13 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 53) 13 53 hvalid hfast

theorem sr13p54:∀ i ∈ List.range 1,StrictCheckAt 13 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 54) 13 54:=by decide +kernel
  have hfast:StrictAtFast (row 13 54) 13 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 54) 13 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 54) 13 54 hvalid hfast

theorem sr13p55:∀ i ∈ List.range 1,StrictCheckAt 13 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 55) 13 55:=by decide +kernel
  have hfast:StrictAtFast (row 13 55) 13 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 55) 13 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 55) 13 55 hvalid hfast

theorem sr13p56:∀ i ∈ List.range 1,StrictCheckAt 13 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 56) 13 56:=by decide +kernel
  have hfast:StrictAtFast (row 13 56) 13 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 56) 13 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 56) 13 56 hvalid hfast

theorem sr13p57:∀ i ∈ List.range 1,StrictCheckAt 13 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 57) 13 57:=by decide +kernel
  have hfast:StrictAtFast (row 13 57) 13 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 57) 13 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 57) 13 57 hvalid hfast

theorem sr13p58:∀ i ∈ List.range 1,StrictCheckAt 13 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 58) 13 58:=by decide +kernel
  have hfast:StrictAtFast (row 13 58) 13 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 58) 13 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 58) 13 58 hvalid hfast

theorem sr13p59:∀ i ∈ List.range 1,StrictCheckAt 13 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 59) 13 59:=by decide +kernel
  have hfast:StrictAtFast (row 13 59) 13 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 59) 13 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 59) 13 59 hvalid hfast

theorem sr13p60:∀ i ∈ List.range 1,StrictCheckAt 13 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 60) 13 60:=by decide +kernel
  have hfast:StrictAtFast (row 13 60) 13 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 60) 13 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 60) 13 60 hvalid hfast

theorem sr13p61:∀ i ∈ List.range 1,StrictCheckAt 13 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 61) 13 61:=by decide +kernel
  have hfast:StrictAtFast (row 13 61) 13 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 61) 13 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 61) 13 61 hvalid hfast

theorem sr13p62:∀ i ∈ List.range 1,StrictCheckAt 13 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 62) 13 62:=by decide +kernel
  have hfast:StrictAtFast (row 13 62) 13 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 62) 13 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 62) 13 62 hvalid hfast

theorem sr13p63:∀ i ∈ List.range 1,StrictCheckAt 13 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 63) 13 63:=by decide +kernel
  have hfast:StrictAtFast (row 13 63) 13 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 63) 13 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 63) 13 63 hvalid hfast

theorem sr13p64:∀ i ∈ List.range 1,StrictCheckAt 13 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 64) 13 64:=by decide +kernel
  have hfast:StrictAtFast (row 13 64) 13 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 64) 13 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 64) 13 64 hvalid hfast

theorem sr13p65:∀ i ∈ List.range 1,StrictCheckAt 13 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 65) 13 65:=by decide +kernel
  have hfast:StrictAtFast (row 13 65) 13 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 65) 13 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 65) 13 65 hvalid hfast

theorem sr13p66:∀ i ∈ List.range 1,StrictCheckAt 13 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 66) 13 66:=by decide +kernel
  have hfast:StrictAtFast (row 13 66) 13 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 66) 13 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 66) 13 66 hvalid hfast

theorem sr13p67:∀ i ∈ List.range 1,StrictCheckAt 13 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 67) 13 67:=by decide +kernel
  have hfast:StrictAtFast (row 13 67) 13 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 67) 13 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 67) 13 67 hvalid hfast

theorem sr13p68:∀ i ∈ List.range 1,StrictCheckAt 13 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 68) 13 68:=by decide +kernel
  have hfast:StrictAtFast (row 13 68) 13 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 68) 13 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 68) 13 68 hvalid hfast

theorem sr13p69:∀ i ∈ List.range 1,StrictCheckAt 13 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 69) 13 69:=by decide +kernel
  have hfast:StrictAtFast (row 13 69) 13 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 69) 13 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 69) 13 69 hvalid hfast

theorem sr13p70:∀ i ∈ List.range 1,StrictCheckAt 13 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 70) 13 70:=by decide +kernel
  have hfast:StrictAtFast (row 13 70) 13 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 70) 13 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 70) 13 70 hvalid hfast

theorem sr13p71:∀ i ∈ List.range 1,StrictCheckAt 13 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 71) 13 71:=by decide +kernel
  have hfast:StrictAtFast (row 13 71) 13 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 71) 13 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 71) 13 71 hvalid hfast

theorem sr13p72:∀ i ∈ List.range 1,StrictCheckAt 13 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 72) 13 72:=by decide +kernel
  have hfast:StrictAtFast (row 13 72) 13 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 72) 13 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 72) 13 72 hvalid hfast

theorem sr13p73:∀ i ∈ List.range 1,StrictCheckAt 13 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 73) 13 73:=by decide +kernel
  have hfast:StrictAtFast (row 13 73) 13 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 73) 13 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 73) 13 73 hvalid hfast

theorem sr13p74:∀ i ∈ List.range 1,StrictCheckAt 13 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 74) 13 74:=by decide +kernel
  have hfast:StrictAtFast (row 13 74) 13 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 74) 13 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 74) 13 74 hvalid hfast

theorem sr13p75:∀ i ∈ List.range 1,StrictCheckAt 13 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 75) 13 75:=by decide +kernel
  have hfast:StrictAtFast (row 13 75) 13 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 75) 13 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 75) 13 75 hvalid hfast

theorem sr13p76:∀ i ∈ List.range 1,StrictCheckAt 13 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 76) 13 76:=by decide +kernel
  have hfast:StrictAtFast (row 13 76) 13 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 76) 13 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 76) 13 76 hvalid hfast

theorem sr13p77:∀ i ∈ List.range 1,StrictCheckAt 13 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 77) 13 77:=by decide +kernel
  have hfast:StrictAtFast (row 13 77) 13 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 77) 13 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 77) 13 77 hvalid hfast

theorem sr13p78:∀ i ∈ List.range 1,StrictCheckAt 13 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 78) 13 78:=by decide +kernel
  have hfast:StrictAtFast (row 13 78) 13 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 78) 13 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 78) 13 78 hvalid hfast

theorem sr13p79:∀ i ∈ List.range 1,StrictCheckAt 13 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 79) 13 79:=by decide +kernel
  have hfast:StrictAtFast (row 13 79) 13 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 79) 13 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 79) 13 79 hvalid hfast

theorem sr13p80:∀ i ∈ List.range 1,StrictCheckAt 13 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 80) 13 80:=by decide +kernel
  have hfast:StrictAtFast (row 13 80) 13 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 80) 13 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 80) 13 80 hvalid hfast

theorem sr13p81:∀ i ∈ List.range 1,StrictCheckAt 13 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 81) 13 81:=by decide +kernel
  have hfast:StrictAtFast (row 13 81) 13 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 81) 13 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 81) 13 81 hvalid hfast

theorem sr13p82:∀ i ∈ List.range 1,StrictCheckAt 13 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 82) 13 82:=by decide +kernel
  have hfast:StrictAtFast (row 13 82) 13 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 82) 13 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 82) 13 82 hvalid hfast

theorem sr13p83:∀ i ∈ List.range 1,StrictCheckAt 13 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 83) 13 83:=by decide +kernel
  have hfast:StrictAtFast (row 13 83) 13 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 83) 13 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 83) 13 83 hvalid hfast

theorem sr13p84:∀ i ∈ List.range 1,StrictCheckAt 13 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 84) 13 84:=by decide +kernel
  have hfast:StrictAtFast (row 13 84) 13 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 84) 13 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 84) 13 84 hvalid hfast

theorem sr13p85:∀ i ∈ List.range 1,StrictCheckAt 13 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 85) 13 85:=by decide +kernel
  have hfast:StrictAtFast (row 13 85) 13 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 85) 13 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 85) 13 85 hvalid hfast

theorem sr13p86:∀ i ∈ List.range 1,StrictCheckAt 13 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 86) 13 86:=by decide +kernel
  have hfast:StrictAtFast (row 13 86) 13 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 86) 13 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 86) 13 86 hvalid hfast

theorem sr13p87:∀ i ∈ List.range 1,StrictCheckAt 13 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 87) 13 87:=by decide +kernel
  have hfast:StrictAtFast (row 13 87) 13 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 87) 13 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 87) 13 87 hvalid hfast

theorem sr13p88:∀ i ∈ List.range 1,StrictCheckAt 13 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 88) 13 88:=by decide +kernel
  have hfast:StrictAtFast (row 13 88) 13 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 88) 13 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 88) 13 88 hvalid hfast

theorem sr13p89:∀ i ∈ List.range 1,StrictCheckAt 13 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 89) 13 89:=by decide +kernel
  have hfast:StrictAtFast (row 13 89) 13 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 89) 13 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 89) 13 89 hvalid hfast

theorem sr13p90:∀ i ∈ List.range 1,StrictCheckAt 13 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 90) 13 90:=by decide +kernel
  have hfast:StrictAtFast (row 13 90) 13 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 90) 13 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 90) 13 90 hvalid hfast

theorem sr13p91:∀ i ∈ List.range 1,StrictCheckAt 13 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 91) 13 91:=by decide +kernel
  have hfast:StrictAtFast (row 13 91) 13 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 91) 13 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 91) 13 91 hvalid hfast

theorem sr13p92:∀ i ∈ List.range 1,StrictCheckAt 13 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 92) 13 92:=by decide +kernel
  have hfast:StrictAtFast (row 13 92) 13 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 92) 13 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 92) 13 92 hvalid hfast

theorem sr13p93:∀ i ∈ List.range 1,StrictCheckAt 13 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 93) 13 93:=by decide +kernel
  have hfast:StrictAtFast (row 13 93) 13 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 93) 13 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 93) 13 93 hvalid hfast

theorem sr13p94:∀ i ∈ List.range 1,StrictCheckAt 13 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 94) 13 94:=by decide +kernel
  have hfast:StrictAtFast (row 13 94) 13 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 94) 13 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 94) 13 94 hvalid hfast

theorem sr13p95:∀ i ∈ List.range 1,StrictCheckAt 13 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 95) 13 95:=by decide +kernel
  have hfast:StrictAtFast (row 13 95) 13 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 95) 13 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 95) 13 95 hvalid hfast

theorem sr13p96:∀ i ∈ List.range 1,StrictCheckAt 13 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 96) 13 96:=by decide +kernel
  have hfast:StrictAtFast (row 13 96) 13 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 96) 13 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 96) 13 96 hvalid hfast

theorem sr13p97:∀ i ∈ List.range 1,StrictCheckAt 13 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 97) 13 97:=by decide +kernel
  have hfast:StrictAtFast (row 13 97) 13 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 97) 13 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 97) 13 97 hvalid hfast

theorem sr13p98:∀ i ∈ List.range 1,StrictCheckAt 13 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 98) 13 98:=by decide +kernel
  have hfast:StrictAtFast (row 13 98) 13 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 98) 13 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 98) 13 98 hvalid hfast

theorem sr13p99:∀ i ∈ List.range 1,StrictCheckAt 13 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 99) 13 99:=by decide +kernel
  have hfast:StrictAtFast (row 13 99) 13 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 99) 13 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 99) 13 99 hvalid hfast

theorem sr13p100:∀ i ∈ List.range 1,StrictCheckAt 13 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 100) 13 100:=by decide +kernel
  have hfast:StrictAtFast (row 13 100) 13 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 100) 13 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 100) 13 100 hvalid hfast

theorem sr13p101:∀ i ∈ List.range 1,StrictCheckAt 13 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 101) 13 101:=by decide +kernel
  have hfast:StrictAtFast (row 13 101) 13 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 101) 13 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 101) 13 101 hvalid hfast

theorem sr13p102:∀ i ∈ List.range 1,StrictCheckAt 13 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 102) 13 102:=by decide +kernel
  have hfast:StrictAtFast (row 13 102) 13 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 102) 13 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 102) 13 102 hvalid hfast

theorem sr13p103:∀ i ∈ List.range 1,StrictCheckAt 13 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 103) 13 103:=by decide +kernel
  have hfast:StrictAtFast (row 13 103) 13 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 103) 13 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 103) 13 103 hvalid hfast

theorem sr13p104:∀ i ∈ List.range 1,StrictCheckAt 13 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 104) 13 104:=by decide +kernel
  have hfast:StrictAtFast (row 13 104) 13 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 104) 13 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 104) 13 104 hvalid hfast

theorem sr13p105:∀ i ∈ List.range 1,StrictCheckAt 13 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 105) 13 105:=by decide +kernel
  have hfast:StrictAtFast (row 13 105) 13 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 105) 13 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 105) 13 105 hvalid hfast

theorem sr13p106:∀ i ∈ List.range 1,StrictCheckAt 13 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 106) 13 106:=by decide +kernel
  have hfast:StrictAtFast (row 13 106) 13 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 106) 13 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 106) 13 106 hvalid hfast

theorem sr13p107:∀ i ∈ List.range 1,StrictCheckAt 13 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 107) 13 107:=by decide +kernel
  have hfast:StrictAtFast (row 13 107) 13 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 107) 13 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 107) 13 107 hvalid hfast

theorem sr13p108:∀ i ∈ List.range 1,StrictCheckAt 13 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 108) 13 108:=by decide +kernel
  have hfast:StrictAtFast (row 13 108) 13 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 108) 13 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 108) 13 108 hvalid hfast

theorem sr13p109:∀ i ∈ List.range 1,StrictCheckAt 13 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 109) 13 109:=by decide +kernel
  have hfast:StrictAtFast (row 13 109) 13 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 109) 13 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 109) 13 109 hvalid hfast

theorem sr13p110:∀ i ∈ List.range 1,StrictCheckAt 13 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 110) 13 110:=by decide +kernel
  have hfast:StrictAtFast (row 13 110) 13 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 110) 13 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 110) 13 110 hvalid hfast

theorem sr13p111:∀ i ∈ List.range 1,StrictCheckAt 13 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 111) 13 111:=by decide +kernel
  have hfast:StrictAtFast (row 13 111) 13 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 111) 13 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 111) 13 111 hvalid hfast

theorem sr13p112:∀ i ∈ List.range 1,StrictCheckAt 13 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 112) 13 112:=by decide +kernel
  have hfast:StrictAtFast (row 13 112) 13 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 112) 13 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 112) 13 112 hvalid hfast

theorem sr13p113:∀ i ∈ List.range 1,StrictCheckAt 13 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 113) 13 113:=by decide +kernel
  have hfast:StrictAtFast (row 13 113) 13 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 113) 13 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 113) 13 113 hvalid hfast

theorem sr13p114:∀ i ∈ List.range 1,StrictCheckAt 13 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 114) 13 114:=by decide +kernel
  have hfast:StrictAtFast (row 13 114) 13 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 114) 13 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 114) 13 114 hvalid hfast

theorem sr13p115:∀ i ∈ List.range 1,StrictCheckAt 13 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 115) 13 115:=by decide +kernel
  have hfast:StrictAtFast (row 13 115) 13 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 115) 13 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 115) 13 115 hvalid hfast

theorem sr13p116:∀ i ∈ List.range 1,StrictCheckAt 13 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 116) 13 116:=by decide +kernel
  have hfast:StrictAtFast (row 13 116) 13 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 116) 13 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 116) 13 116 hvalid hfast

theorem sr13p117:∀ i ∈ List.range 1,StrictCheckAt 13 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 117) 13 117:=by decide +kernel
  have hfast:StrictAtFast (row 13 117) 13 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 117) 13 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 117) 13 117 hvalid hfast

theorem sr13p118:∀ i ∈ List.range 1,StrictCheckAt 13 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 118) 13 118:=by decide +kernel
  have hfast:StrictAtFast (row 13 118) 13 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 118) 13 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 118) 13 118 hvalid hfast

theorem sr13p119:∀ i ∈ List.range 1,StrictCheckAt 13 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 119) 13 119:=by decide +kernel
  have hfast:StrictAtFast (row 13 119) 13 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 119) 13 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 119) 13 119 hvalid hfast

theorem sr13p120:∀ i ∈ List.range 1,StrictCheckAt 13 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 120) 13 120:=by decide +kernel
  have hfast:StrictAtFast (row 13 120) 13 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 120) 13 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 120) 13 120 hvalid hfast

theorem sr13p121:∀ i ∈ List.range 1,StrictCheckAt 13 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 121) 13 121:=by decide +kernel
  have hfast:StrictAtFast (row 13 121) 13 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 121) 13 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 121) 13 121 hvalid hfast

theorem sr13p122:∀ i ∈ List.range 1,StrictCheckAt 13 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 122) 13 122:=by decide +kernel
  have hfast:StrictAtFast (row 13 122) 13 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 122) 13 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 122) 13 122 hvalid hfast

theorem sr13p123:∀ i ∈ List.range 1,StrictCheckAt 13 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 123) 13 123:=by decide +kernel
  have hfast:StrictAtFast (row 13 123) 13 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 123) 13 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 123) 13 123 hvalid hfast

theorem sr13p124:∀ i ∈ List.range 1,StrictCheckAt 13 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 124) 13 124:=by decide +kernel
  have hfast:StrictAtFast (row 13 124) 13 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 124) 13 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 124) 13 124 hvalid hfast

theorem sr13p125:∀ i ∈ List.range 1,StrictCheckAt 13 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 125) 13 125:=by decide +kernel
  have hfast:StrictAtFast (row 13 125) 13 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 125) 13 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 125) 13 125 hvalid hfast

theorem sr13p126:∀ i ∈ List.range 1,StrictCheckAt 13 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 126) 13 126:=by decide +kernel
  have hfast:StrictAtFast (row 13 126) 13 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 126) 13 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 126) 13 126 hvalid hfast

theorem sr13p127:∀ i ∈ List.range 1,StrictCheckAt 13 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 127) 13 127:=by decide +kernel
  have hfast:StrictAtFast (row 13 127) 13 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 127) 13 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 127) 13 127 hvalid hfast

theorem sr13p128:∀ i ∈ List.range 1,StrictCheckAt 13 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 128) 13 128:=by decide +kernel
  have hfast:StrictAtFast (row 13 128) 13 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 128) 13 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 128) 13 128 hvalid hfast

theorem sr13p129:∀ i ∈ List.range 1,StrictCheckAt 13 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 129) 13 129:=by decide +kernel
  have hfast:StrictAtFast (row 13 129) 13 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 129) 13 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 129) 13 129 hvalid hfast

theorem br13p0:∀ i ∈ List.range 4,BaseCheckAt 13 (0+i):=by decide +kernel

theorem br13p1:∀ i ∈ List.range 4,BaseCheckAt 13 (4+i):=by decide +kernel

theorem br13p2:∀ i ∈ List.range 4,BaseCheckAt 13 (8+i):=by decide +kernel

theorem br13p3:∀ i ∈ List.range 4,BaseCheckAt 13 (12+i):=by decide +kernel

theorem br13p4:∀ i ∈ List.range 4,BaseCheckAt 13 (16+i):=by decide +kernel

theorem br13p5:∀ i ∈ List.range 4,BaseCheckAt 13 (20+i):=by decide +kernel

theorem br13p6:∀ i ∈ List.range 4,BaseCheckAt 13 (24+i):=by decide +kernel

theorem br13p7:∀ i ∈ List.range 4,BaseCheckAt 13 (28+i):=by decide +kernel

theorem br13p8:∀ i ∈ List.range 4,BaseCheckAt 13 (32+i):=by decide +kernel

theorem br13p9:∀ i ∈ List.range 4,BaseCheckAt 13 (36+i):=by decide +kernel

theorem br13p10:∀ i ∈ List.range 4,BaseCheckAt 13 (40+i):=by decide +kernel

theorem br13p11:∀ i ∈ List.range 4,BaseCheckAt 13 (44+i):=by decide +kernel

theorem br13p12:∀ i ∈ List.range 4,BaseCheckAt 13 (48+i):=by decide +kernel

theorem br13p13:∀ i ∈ List.range 4,BaseCheckAt 13 (52+i):=by decide +kernel

theorem br13p14:∀ i ∈ List.range 4,BaseCheckAt 13 (56+i):=by decide +kernel

theorem br13p15:∀ i ∈ List.range 4,BaseCheckAt 13 (60+i):=by decide +kernel



theorem br13p16:∀ i ∈ List.range 4,BaseCheckAt 13 (64+i):=by decide +kernel

theorem br13p17:∀ i ∈ List.range 4,BaseCheckAt 13 (68+i):=by decide +kernel

theorem br13p18:∀ i ∈ List.range 4,BaseCheckAt 13 (72+i):=by decide +kernel

theorem br13p19:∀ i ∈ List.range 4,BaseCheckAt 13 (76+i):=by decide +kernel

theorem br13p20:∀ i ∈ List.range 4,BaseCheckAt 13 (80+i):=by decide +kernel

theorem br13p21:∀ i ∈ List.range 4,BaseCheckAt 13 (84+i):=by decide +kernel

theorem br13p22:∀ i ∈ List.range 4,BaseCheckAt 13 (88+i):=by decide +kernel

theorem br13p23:∀ i ∈ List.range 4,BaseCheckAt 13 (92+i):=by decide +kernel

theorem br13p24:∀ i ∈ List.range 4,BaseCheckAt 13 (96+i):=by decide +kernel

theorem br13p25:∀ i ∈ List.range 4,BaseCheckAt 13 (100+i):=by decide +kernel

theorem br13p26:∀ i ∈ List.range 4,BaseCheckAt 13 (104+i):=by decide +kernel

theorem br13p27:∀ i ∈ List.range 4,BaseCheckAt 13 (108+i):=by decide +kernel

theorem br13p28:∀ i ∈ List.range 4,BaseCheckAt 13 (112+i):=by decide +kernel

theorem br13p29:∀ i ∈ List.range 4,BaseCheckAt 13 (116+i):=by decide +kernel

theorem br13p30:∀ i ∈ List.range 4,BaseCheckAt 13 (120+i):=by decide +kernel

theorem br13p31:∀ i ∈ List.range 4,BaseCheckAt 13 (124+i):=by decide +kernel



theorem br13p32:∀ i ∈ List.range 2,BaseCheckAt 13 (128+i):=by decide +kernel



theorem cr13:∀ V ∈ List.range 130,CorrectAt 13 V:=by
  intro V hV
  have hv:V < 130:=List.mem_range.mp hV
  by_cases h0_17:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr13p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr13p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr13p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr13p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr13p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr13p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr13p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr13p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_17:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr13p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr13p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr13p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr13p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_17:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr13p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr13p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_17:V < 120
        · have h:=cr13p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h15_17:V < 128
          · have h:=cr13p15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=cr13p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem zr13:∀ V ∈ List.range 130,ZeroCheckAt 13 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 13 V (by omega) (by omega) (by omega)
theorem sr13:∀ V ∈ List.range 130,StrictCheckAt 13 V:=by
  intro V hV
  have hv:V < 130:=List.mem_range.mp hV
  by_cases h0_130:V < 65
  · by_cases h0_65:V < 32
    · by_cases h0_32:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have h:=sr13p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
              · have h:=sr13p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
            · by_cases h2_4:V < 3
              · have h:=sr13p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
              · have h:=sr13p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have h:=sr13p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
              · have h:=sr13p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
            · by_cases h6_8:V < 7
              · have h:=sr13p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
              · have h:=sr13p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have h:=sr13p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr13p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
            · by_cases h10_12:V < 11
              · have h:=sr13p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr13p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have h:=sr13p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr13p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
            · by_cases h14_16:V < 15
              · have h:=sr13p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
              · have h:=sr13p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
      · by_cases h16_32:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have h:=sr13p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr13p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
            · by_cases h18_20:V < 19
              · have h:=sr13p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr13p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have h:=sr13p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr13p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr13p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr13p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
        · by_cases h24_32:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr13p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr13p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr13p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr13p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
          · by_cases h28_32:V < 30
            · by_cases h28_30:V < 29
              · have h:=sr13p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr13p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_32:V < 31
              · have h:=sr13p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · have h:=sr13p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
    · by_cases h32_65:V < 48
      · by_cases h32_48:V < 40
        · by_cases h32_40:V < 36
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have h:=sr13p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr13p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
            · by_cases h34_36:V < 35
              · have h:=sr13p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr13p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have h:=sr13p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr13p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
            · by_cases h38_40:V < 39
              · have h:=sr13p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr13p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
        · by_cases h40_48:V < 44
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have h:=sr13p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr13p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
            · by_cases h42_44:V < 43
              · have h:=sr13p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr13p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
          · by_cases h44_48:V < 46
            · by_cases h44_46:V < 45
              · have h:=sr13p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr13p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
            · by_cases h46_48:V < 47
              · have h:=sr13p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr13p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
      · by_cases h48_65:V < 56
        · by_cases h48_56:V < 52
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have h:=sr13p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr13p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
            · by_cases h50_52:V < 51
              · have h:=sr13p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr13p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have h:=sr13p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr13p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
            · by_cases h54_56:V < 55
              · have h:=sr13p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr13p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
        · by_cases h56_65:V < 60
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have h:=sr13p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr13p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
            · by_cases h58_60:V < 59
              · have h:=sr13p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr13p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
          · by_cases h60_65:V < 62
            · by_cases h60_62:V < 61
              · have h:=sr13p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr13p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
            · by_cases h62_65:V < 63
              · have h:=sr13p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · by_cases h63_65:V < 64
                · have h:=sr13p63 (V-63) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
                · have h:=sr13p64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
  · by_cases h65_130:V < 97
    · by_cases h65_97:V < 81
      · by_cases h65_81:V < 73
        · by_cases h65_73:V < 69
          · by_cases h65_69:V < 67
            · by_cases h65_67:V < 66
              · have h:=sr13p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr13p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
            · by_cases h67_69:V < 68
              · have h:=sr13p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr13p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have h:=sr13p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr13p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
            · by_cases h71_73:V < 72
              · have h:=sr13p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr13p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h73_81:V < 77
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have h:=sr13p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr13p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
            · by_cases h75_77:V < 76
              · have h:=sr13p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr13p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have h:=sr13p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr13p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
            · by_cases h79_81:V < 80
              · have h:=sr13p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr13p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
      · by_cases h81_97:V < 89
        · by_cases h81_89:V < 85
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have h:=sr13p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr13p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
            · by_cases h83_85:V < 84
              · have h:=sr13p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr13p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have h:=sr13p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr13p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
            · by_cases h87_89:V < 88
              · have h:=sr13p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr13p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h89_97:V < 93
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have h:=sr13p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr13p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr13p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr13p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have h:=sr13p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr13p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
            · by_cases h95_97:V < 96
              · have h:=sr13p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr13p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
    · by_cases h97_130:V < 113
      · by_cases h97_113:V < 105
        · by_cases h97_105:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have h:=sr13p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr13p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_101:V < 100
              · have h:=sr13p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr13p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have h:=sr13p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr13p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr13p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr13p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h105_113:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have h:=sr13p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr13p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
            · by_cases h107_109:V < 108
              · have h:=sr13p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr13p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have h:=sr13p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr13p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
            · by_cases h111_113:V < 112
              · have h:=sr13p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr13p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
      · by_cases h113_130:V < 121
        · by_cases h113_121:V < 117
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have h:=sr13p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr13p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
            · by_cases h115_117:V < 116
              · have h:=sr13p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr13p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · by_cases h117_121:V < 119
            · by_cases h117_119:V < 118
              · have h:=sr13p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
              · have h:=sr13p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
            · by_cases h119_121:V < 120
              · have h:=sr13p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
              · have h:=sr13p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
        · by_cases h121_130:V < 125
          · by_cases h121_125:V < 123
            · by_cases h121_123:V < 122
              · have h:=sr13p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
              · have h:=sr13p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
            · by_cases h123_125:V < 124
              · have h:=sr13p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
              · have h:=sr13p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
          · by_cases h125_130:V < 127
            · by_cases h125_127:V < 126
              · have h:=sr13p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
              · have h:=sr13p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h
            · by_cases h127_130:V < 128
              · have h:=sr13p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using h
              · by_cases h128_130:V < 129
                · have h:=sr13p128 (V-128) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
                · have h:=sr13p129 (V-129) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using h

theorem br13:∀ V ∈ List.range 130,BaseCheckAt 13 V:=by
  intro V hV
  have hv:V < 130:=List.mem_range.mp hV
  by_cases h0_33:V < 64
  · by_cases h0_16:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br13p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br13p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br13p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br13p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br13p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br13p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br13p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br13p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_16:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br13p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br13p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br13p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br13p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_16:V < 56
        · by_cases h12_14:V < 52
          · have h:=br13p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br13p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_16:V < 60
          · have h:=br13p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · have h:=br13p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h16_33:V < 96
    · by_cases h16_24:V < 80
      · by_cases h16_20:V < 72
        · by_cases h16_18:V < 68
          · have h:=br13p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br13p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h18_20:V < 76
          · have h:=br13p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br13p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h20_24:V < 88
        · by_cases h20_22:V < 84
          · have h:=br13p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br13p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br13p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br13p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h24_33:V < 112
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br13p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br13p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br13p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br13p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h28_33:V < 120
        · by_cases h28_30:V < 116
          · have h:=br13p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br13p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h30_33:V < 124
          · have h:=br13p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · by_cases h31_33:V < 128
            · have h:=br13p31 (V-124) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
            · have h:=br13p32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
