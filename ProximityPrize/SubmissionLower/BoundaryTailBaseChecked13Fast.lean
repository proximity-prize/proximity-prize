import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
