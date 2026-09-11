import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
