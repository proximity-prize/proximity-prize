import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
