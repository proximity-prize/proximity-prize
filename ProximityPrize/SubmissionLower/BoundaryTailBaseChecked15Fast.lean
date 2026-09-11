import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr15p0:∀ i ∈ List.range 8,CorrectAt 15 (0+i):=by decide +kernel

theorem cr15p1:∀ i ∈ List.range 8,CorrectAt 15 (8+i):=by decide +kernel

theorem cr15p2:∀ i ∈ List.range 8,CorrectAt 15 (16+i):=by decide +kernel

theorem cr15p3:∀ i ∈ List.range 8,CorrectAt 15 (24+i):=by decide +kernel

theorem cr15p4:∀ i ∈ List.range 8,CorrectAt 15 (32+i):=by decide +kernel

theorem cr15p5:∀ i ∈ List.range 8,CorrectAt 15 (40+i):=by decide +kernel

theorem cr15p6:∀ i ∈ List.range 8,CorrectAt 15 (48+i):=by decide +kernel

theorem cr15p7:∀ i ∈ List.range 8,CorrectAt 15 (56+i):=by decide +kernel

theorem cr15p8:∀ i ∈ List.range 8,CorrectAt 15 (64+i):=by decide +kernel

theorem cr15p9:∀ i ∈ List.range 8,CorrectAt 15 (72+i):=by decide +kernel

theorem cr15p10:∀ i ∈ List.range 8,CorrectAt 15 (80+i):=by decide +kernel

theorem cr15p11:∀ i ∈ List.range 8,CorrectAt 15 (88+i):=by decide +kernel

theorem cr15p12:∀ i ∈ List.range 8,CorrectAt 15 (96+i):=by decide +kernel

theorem cr15p13:∀ i ∈ List.range 8,CorrectAt 15 (104+i):=by decide +kernel

theorem cr15p14:∀ i ∈ List.range 8,CorrectAt 15 (112+i):=by decide +kernel

theorem cr15p15:∀ i ∈ List.range 8,CorrectAt 15 (120+i):=by decide +kernel

theorem sr15p0:∀ i ∈ List.range 1,StrictCheckAt 15 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 0) 15 0:=by decide +kernel
  have hfast:StrictAtFast (row 15 0) 15 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 0) 15 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 0) 15 0 hvalid hfast

theorem sr15p1:∀ i ∈ List.range 1,StrictCheckAt 15 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 1) 15 1:=by decide +kernel
  have hfast:StrictAtFast (row 15 1) 15 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 1) 15 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 1) 15 1 hvalid hfast

theorem sr15p2:∀ i ∈ List.range 1,StrictCheckAt 15 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 2) 15 2:=by decide +kernel
  have hfast:StrictAtFast (row 15 2) 15 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 2) 15 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 2) 15 2 hvalid hfast

theorem sr15p3:∀ i ∈ List.range 1,StrictCheckAt 15 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 3) 15 3:=by decide +kernel
  have hfast:StrictAtFast (row 15 3) 15 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 3) 15 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 3) 15 3 hvalid hfast

theorem sr15p4:∀ i ∈ List.range 1,StrictCheckAt 15 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 4) 15 4:=by decide +kernel
  have hfast:StrictAtFast (row 15 4) 15 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 4) 15 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 4) 15 4 hvalid hfast

theorem sr15p5:∀ i ∈ List.range 1,StrictCheckAt 15 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 5) 15 5:=by decide +kernel
  have hfast:StrictAtFast (row 15 5) 15 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 5) 15 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 5) 15 5 hvalid hfast

theorem sr15p6:∀ i ∈ List.range 1,StrictCheckAt 15 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 6) 15 6:=by decide +kernel
  have hfast:StrictAtFast (row 15 6) 15 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 6) 15 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 6) 15 6 hvalid hfast

theorem sr15p7:∀ i ∈ List.range 1,StrictCheckAt 15 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 7) 15 7:=by decide +kernel
  have hfast:StrictAtFast (row 15 7) 15 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 7) 15 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 7) 15 7 hvalid hfast

theorem sr15p8:∀ i ∈ List.range 1,StrictCheckAt 15 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 8) 15 8:=by decide +kernel
  have hfast:StrictAtFast (row 15 8) 15 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 8) 15 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 8) 15 8 hvalid hfast

theorem sr15p9:∀ i ∈ List.range 1,StrictCheckAt 15 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 9) 15 9:=by decide +kernel
  have hfast:StrictAtFast (row 15 9) 15 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 9) 15 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 9) 15 9 hvalid hfast

theorem sr15p10:∀ i ∈ List.range 1,StrictCheckAt 15 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 10) 15 10:=by decide +kernel
  have hfast:StrictAtFast (row 15 10) 15 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 10) 15 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 10) 15 10 hvalid hfast

theorem sr15p11:∀ i ∈ List.range 1,StrictCheckAt 15 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 11) 15 11:=by decide +kernel
  have hfast:StrictAtFast (row 15 11) 15 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 11) 15 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 11) 15 11 hvalid hfast

theorem sr15p12:∀ i ∈ List.range 1,StrictCheckAt 15 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 12) 15 12:=by decide +kernel
  have hfast:StrictAtFast (row 15 12) 15 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 12) 15 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 12) 15 12 hvalid hfast

theorem sr15p13:∀ i ∈ List.range 1,StrictCheckAt 15 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 13) 15 13:=by decide +kernel
  have hfast:StrictAtFast (row 15 13) 15 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 13) 15 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 13) 15 13 hvalid hfast

theorem sr15p14:∀ i ∈ List.range 1,StrictCheckAt 15 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 14) 15 14:=by decide +kernel
  have hfast:StrictAtFast (row 15 14) 15 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 14) 15 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 14) 15 14 hvalid hfast

theorem sr15p15:∀ i ∈ List.range 1,StrictCheckAt 15 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 15) 15 15:=by decide +kernel
  have hfast:StrictAtFast (row 15 15) 15 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 15) 15 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 15) 15 15 hvalid hfast

theorem sr15p16:∀ i ∈ List.range 1,StrictCheckAt 15 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 16) 15 16:=by decide +kernel
  have hfast:StrictAtFast (row 15 16) 15 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 16) 15 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 16) 15 16 hvalid hfast

theorem sr15p17:∀ i ∈ List.range 1,StrictCheckAt 15 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 17) 15 17:=by decide +kernel
  have hfast:StrictAtFast (row 15 17) 15 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 17) 15 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 17) 15 17 hvalid hfast

theorem sr15p18:∀ i ∈ List.range 1,StrictCheckAt 15 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 18) 15 18:=by decide +kernel
  have hfast:StrictAtFast (row 15 18) 15 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 18) 15 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 18) 15 18 hvalid hfast

theorem sr15p19:∀ i ∈ List.range 1,StrictCheckAt 15 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 19) 15 19:=by decide +kernel
  have hfast:StrictAtFast (row 15 19) 15 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 19) 15 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 19) 15 19 hvalid hfast

theorem sr15p20:∀ i ∈ List.range 1,StrictCheckAt 15 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 20) 15 20:=by decide +kernel
  have hfast:StrictAtFast (row 15 20) 15 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 20) 15 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 20) 15 20 hvalid hfast

theorem sr15p21:∀ i ∈ List.range 1,StrictCheckAt 15 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 21) 15 21:=by decide +kernel
  have hfast:StrictAtFast (row 15 21) 15 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 21) 15 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 21) 15 21 hvalid hfast

theorem sr15p22:∀ i ∈ List.range 1,StrictCheckAt 15 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 22) 15 22:=by decide +kernel
  have hfast:StrictAtFast (row 15 22) 15 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 22) 15 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 22) 15 22 hvalid hfast

theorem sr15p23:∀ i ∈ List.range 1,StrictCheckAt 15 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 23) 15 23:=by decide +kernel
  have hfast:StrictAtFast (row 15 23) 15 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 23) 15 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 23) 15 23 hvalid hfast

theorem sr15p24:∀ i ∈ List.range 1,StrictCheckAt 15 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 24) 15 24:=by decide +kernel
  have hfast:StrictAtFast (row 15 24) 15 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 24) 15 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 24) 15 24 hvalid hfast

theorem sr15p25:∀ i ∈ List.range 1,StrictCheckAt 15 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 25) 15 25:=by decide +kernel
  have hfast:StrictAtFast (row 15 25) 15 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 25) 15 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 25) 15 25 hvalid hfast

theorem sr15p26:∀ i ∈ List.range 1,StrictCheckAt 15 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 26) 15 26:=by decide +kernel
  have hfast:StrictAtFast (row 15 26) 15 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 26) 15 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 26) 15 26 hvalid hfast

theorem sr15p27:∀ i ∈ List.range 1,StrictCheckAt 15 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 27) 15 27:=by decide +kernel
  have hfast:StrictAtFast (row 15 27) 15 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 27) 15 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 27) 15 27 hvalid hfast

theorem sr15p28:∀ i ∈ List.range 1,StrictCheckAt 15 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 28) 15 28:=by decide +kernel
  have hfast:StrictAtFast (row 15 28) 15 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 28) 15 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 28) 15 28 hvalid hfast

theorem sr15p29:∀ i ∈ List.range 1,StrictCheckAt 15 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 29) 15 29:=by decide +kernel
  have hfast:StrictAtFast (row 15 29) 15 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 29) 15 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 29) 15 29 hvalid hfast

theorem sr15p30:∀ i ∈ List.range 1,StrictCheckAt 15 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 30) 15 30:=by decide +kernel
  have hfast:StrictAtFast (row 15 30) 15 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 30) 15 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 30) 15 30 hvalid hfast

theorem sr15p31:∀ i ∈ List.range 1,StrictCheckAt 15 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 31) 15 31:=by decide +kernel
  have hfast:StrictAtFast (row 15 31) 15 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 31) 15 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 31) 15 31 hvalid hfast

theorem sr15p32:∀ i ∈ List.range 1,StrictCheckAt 15 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 32) 15 32:=by decide +kernel
  have hfast:StrictAtFast (row 15 32) 15 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 32) 15 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 32) 15 32 hvalid hfast

theorem sr15p33:∀ i ∈ List.range 1,StrictCheckAt 15 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 33) 15 33:=by decide +kernel
  have hfast:StrictAtFast (row 15 33) 15 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 33) 15 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 33) 15 33 hvalid hfast

theorem sr15p34:∀ i ∈ List.range 1,StrictCheckAt 15 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 34) 15 34:=by decide +kernel
  have hfast:StrictAtFast (row 15 34) 15 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 34) 15 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 34) 15 34 hvalid hfast

theorem sr15p35:∀ i ∈ List.range 1,StrictCheckAt 15 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 35) 15 35:=by decide +kernel
  have hfast:StrictAtFast (row 15 35) 15 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 35) 15 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 35) 15 35 hvalid hfast

theorem sr15p36:∀ i ∈ List.range 1,StrictCheckAt 15 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 36) 15 36:=by decide +kernel
  have hfast:StrictAtFast (row 15 36) 15 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 36) 15 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 36) 15 36 hvalid hfast

theorem sr15p37:∀ i ∈ List.range 1,StrictCheckAt 15 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 37) 15 37:=by decide +kernel
  have hfast:StrictAtFast (row 15 37) 15 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 37) 15 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 37) 15 37 hvalid hfast

theorem sr15p38:∀ i ∈ List.range 1,StrictCheckAt 15 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 38) 15 38:=by decide +kernel
  have hfast:StrictAtFast (row 15 38) 15 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 38) 15 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 38) 15 38 hvalid hfast

theorem sr15p39:∀ i ∈ List.range 1,StrictCheckAt 15 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 39) 15 39:=by decide +kernel
  have hfast:StrictAtFast (row 15 39) 15 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 39) 15 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 39) 15 39 hvalid hfast

theorem sr15p40:∀ i ∈ List.range 1,StrictCheckAt 15 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 40) 15 40:=by decide +kernel
  have hfast:StrictAtFast (row 15 40) 15 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 40) 15 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 40) 15 40 hvalid hfast

theorem sr15p41:∀ i ∈ List.range 1,StrictCheckAt 15 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 41) 15 41:=by decide +kernel
  have hfast:StrictAtFast (row 15 41) 15 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 41) 15 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 41) 15 41 hvalid hfast

theorem sr15p42:∀ i ∈ List.range 1,StrictCheckAt 15 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 42) 15 42:=by decide +kernel
  have hfast:StrictAtFast (row 15 42) 15 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 42) 15 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 42) 15 42 hvalid hfast

theorem sr15p43:∀ i ∈ List.range 1,StrictCheckAt 15 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 43) 15 43:=by decide +kernel
  have hfast:StrictAtFast (row 15 43) 15 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 43) 15 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 43) 15 43 hvalid hfast

theorem sr15p44:∀ i ∈ List.range 1,StrictCheckAt 15 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 44) 15 44:=by decide +kernel
  have hfast:StrictAtFast (row 15 44) 15 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 44) 15 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 44) 15 44 hvalid hfast

theorem sr15p45:∀ i ∈ List.range 1,StrictCheckAt 15 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 45) 15 45:=by decide +kernel
  have hfast:StrictAtFast (row 15 45) 15 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 45) 15 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 45) 15 45 hvalid hfast

theorem sr15p46:∀ i ∈ List.range 1,StrictCheckAt 15 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 46) 15 46:=by decide +kernel
  have hfast:StrictAtFast (row 15 46) 15 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 46) 15 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 46) 15 46 hvalid hfast

theorem sr15p47:∀ i ∈ List.range 1,StrictCheckAt 15 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 47) 15 47:=by decide +kernel
  have hfast:StrictAtFast (row 15 47) 15 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 47) 15 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 47) 15 47 hvalid hfast

theorem sr15p48:∀ i ∈ List.range 1,StrictCheckAt 15 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 48) 15 48:=by decide +kernel
  have hfast:StrictAtFast (row 15 48) 15 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 48) 15 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 48) 15 48 hvalid hfast

theorem sr15p49:∀ i ∈ List.range 1,StrictCheckAt 15 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 49) 15 49:=by decide +kernel
  have hfast:StrictAtFast (row 15 49) 15 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 49) 15 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 49) 15 49 hvalid hfast

theorem sr15p50:∀ i ∈ List.range 1,StrictCheckAt 15 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 50) 15 50:=by decide +kernel
  have hfast:StrictAtFast (row 15 50) 15 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 50) 15 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 50) 15 50 hvalid hfast

theorem sr15p51:∀ i ∈ List.range 1,StrictCheckAt 15 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 51) 15 51:=by decide +kernel
  have hfast:StrictAtFast (row 15 51) 15 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 51) 15 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 51) 15 51 hvalid hfast

theorem sr15p52:∀ i ∈ List.range 1,StrictCheckAt 15 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 52) 15 52:=by decide +kernel
  have hfast:StrictAtFast (row 15 52) 15 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 52) 15 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 52) 15 52 hvalid hfast

theorem sr15p53:∀ i ∈ List.range 1,StrictCheckAt 15 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 53) 15 53:=by decide +kernel
  have hfast:StrictAtFast (row 15 53) 15 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 53) 15 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 53) 15 53 hvalid hfast

theorem sr15p54:∀ i ∈ List.range 1,StrictCheckAt 15 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 54) 15 54:=by decide +kernel
  have hfast:StrictAtFast (row 15 54) 15 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 54) 15 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 54) 15 54 hvalid hfast

theorem sr15p55:∀ i ∈ List.range 1,StrictCheckAt 15 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 55) 15 55:=by decide +kernel
  have hfast:StrictAtFast (row 15 55) 15 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 55) 15 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 55) 15 55 hvalid hfast

theorem sr15p56:∀ i ∈ List.range 1,StrictCheckAt 15 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 56) 15 56:=by decide +kernel
  have hfast:StrictAtFast (row 15 56) 15 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 56) 15 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 56) 15 56 hvalid hfast

theorem sr15p57:∀ i ∈ List.range 1,StrictCheckAt 15 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 57) 15 57:=by decide +kernel
  have hfast:StrictAtFast (row 15 57) 15 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 57) 15 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 57) 15 57 hvalid hfast

theorem sr15p58:∀ i ∈ List.range 1,StrictCheckAt 15 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 58) 15 58:=by decide +kernel
  have hfast:StrictAtFast (row 15 58) 15 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 58) 15 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 58) 15 58 hvalid hfast

theorem sr15p59:∀ i ∈ List.range 1,StrictCheckAt 15 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 59) 15 59:=by decide +kernel
  have hfast:StrictAtFast (row 15 59) 15 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 59) 15 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 59) 15 59 hvalid hfast

theorem sr15p60:∀ i ∈ List.range 1,StrictCheckAt 15 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 60) 15 60:=by decide +kernel
  have hfast:StrictAtFast (row 15 60) 15 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 60) 15 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 60) 15 60 hvalid hfast

theorem sr15p61:∀ i ∈ List.range 1,StrictCheckAt 15 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 61) 15 61:=by decide +kernel
  have hfast:StrictAtFast (row 15 61) 15 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 61) 15 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 61) 15 61 hvalid hfast

theorem sr15p62:∀ i ∈ List.range 1,StrictCheckAt 15 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 62) 15 62:=by decide +kernel
  have hfast:StrictAtFast (row 15 62) 15 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 62) 15 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 62) 15 62 hvalid hfast

theorem sr15p63:∀ i ∈ List.range 1,StrictCheckAt 15 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 63) 15 63:=by decide +kernel
  have hfast:StrictAtFast (row 15 63) 15 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 63) 15 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 63) 15 63 hvalid hfast

theorem sr15p64:∀ i ∈ List.range 1,StrictCheckAt 15 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 64) 15 64:=by decide +kernel
  have hfast:StrictAtFast (row 15 64) 15 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 64) 15 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 64) 15 64 hvalid hfast

theorem sr15p65:∀ i ∈ List.range 1,StrictCheckAt 15 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 65) 15 65:=by decide +kernel
  have hfast:StrictAtFast (row 15 65) 15 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 65) 15 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 65) 15 65 hvalid hfast

theorem sr15p66:∀ i ∈ List.range 1,StrictCheckAt 15 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 66) 15 66:=by decide +kernel
  have hfast:StrictAtFast (row 15 66) 15 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 66) 15 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 66) 15 66 hvalid hfast

theorem sr15p67:∀ i ∈ List.range 1,StrictCheckAt 15 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 67) 15 67:=by decide +kernel
  have hfast:StrictAtFast (row 15 67) 15 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 67) 15 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 67) 15 67 hvalid hfast

theorem sr15p68:∀ i ∈ List.range 1,StrictCheckAt 15 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 68) 15 68:=by decide +kernel
  have hfast:StrictAtFast (row 15 68) 15 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 68) 15 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 68) 15 68 hvalid hfast

theorem sr15p69:∀ i ∈ List.range 1,StrictCheckAt 15 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 69) 15 69:=by decide +kernel
  have hfast:StrictAtFast (row 15 69) 15 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 69) 15 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 69) 15 69 hvalid hfast

theorem sr15p70:∀ i ∈ List.range 1,StrictCheckAt 15 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 70) 15 70:=by decide +kernel
  have hfast:StrictAtFast (row 15 70) 15 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 70) 15 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 70) 15 70 hvalid hfast

theorem sr15p71:∀ i ∈ List.range 1,StrictCheckAt 15 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 71) 15 71:=by decide +kernel
  have hfast:StrictAtFast (row 15 71) 15 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 71) 15 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 71) 15 71 hvalid hfast

theorem sr15p72:∀ i ∈ List.range 1,StrictCheckAt 15 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 72) 15 72:=by decide +kernel
  have hfast:StrictAtFast (row 15 72) 15 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 72) 15 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 72) 15 72 hvalid hfast

theorem sr15p73:∀ i ∈ List.range 1,StrictCheckAt 15 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 73) 15 73:=by decide +kernel
  have hfast:StrictAtFast (row 15 73) 15 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 73) 15 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 73) 15 73 hvalid hfast

theorem sr15p74:∀ i ∈ List.range 1,StrictCheckAt 15 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 74) 15 74:=by decide +kernel
  have hfast:StrictAtFast (row 15 74) 15 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 74) 15 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 74) 15 74 hvalid hfast

theorem sr15p75:∀ i ∈ List.range 1,StrictCheckAt 15 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 75) 15 75:=by decide +kernel
  have hfast:StrictAtFast (row 15 75) 15 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 75) 15 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 75) 15 75 hvalid hfast

theorem sr15p76:∀ i ∈ List.range 1,StrictCheckAt 15 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 76) 15 76:=by decide +kernel
  have hfast:StrictAtFast (row 15 76) 15 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 76) 15 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 76) 15 76 hvalid hfast

theorem sr15p77:∀ i ∈ List.range 1,StrictCheckAt 15 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 77) 15 77:=by decide +kernel
  have hfast:StrictAtFast (row 15 77) 15 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 77) 15 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 77) 15 77 hvalid hfast

theorem sr15p78:∀ i ∈ List.range 1,StrictCheckAt 15 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 78) 15 78:=by decide +kernel
  have hfast:StrictAtFast (row 15 78) 15 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 78) 15 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 78) 15 78 hvalid hfast

theorem sr15p79:∀ i ∈ List.range 1,StrictCheckAt 15 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 79) 15 79:=by decide +kernel
  have hfast:StrictAtFast (row 15 79) 15 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 79) 15 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 79) 15 79 hvalid hfast

theorem sr15p80:∀ i ∈ List.range 1,StrictCheckAt 15 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 80) 15 80:=by decide +kernel
  have hfast:StrictAtFast (row 15 80) 15 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 80) 15 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 80) 15 80 hvalid hfast

theorem sr15p81:∀ i ∈ List.range 1,StrictCheckAt 15 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 81) 15 81:=by decide +kernel
  have hfast:StrictAtFast (row 15 81) 15 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 81) 15 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 81) 15 81 hvalid hfast

theorem sr15p82:∀ i ∈ List.range 1,StrictCheckAt 15 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 82) 15 82:=by decide +kernel
  have hfast:StrictAtFast (row 15 82) 15 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 82) 15 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 82) 15 82 hvalid hfast

theorem sr15p83:∀ i ∈ List.range 1,StrictCheckAt 15 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 83) 15 83:=by decide +kernel
  have hfast:StrictAtFast (row 15 83) 15 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 83) 15 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 83) 15 83 hvalid hfast

theorem sr15p84:∀ i ∈ List.range 1,StrictCheckAt 15 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 84) 15 84:=by decide +kernel
  have hfast:StrictAtFast (row 15 84) 15 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 84) 15 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 84) 15 84 hvalid hfast

theorem sr15p85:∀ i ∈ List.range 1,StrictCheckAt 15 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 85) 15 85:=by decide +kernel
  have hfast:StrictAtFast (row 15 85) 15 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 85) 15 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 85) 15 85 hvalid hfast

theorem sr15p86:∀ i ∈ List.range 1,StrictCheckAt 15 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 86) 15 86:=by decide +kernel
  have hfast:StrictAtFast (row 15 86) 15 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 86) 15 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 86) 15 86 hvalid hfast

theorem sr15p87:∀ i ∈ List.range 1,StrictCheckAt 15 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 87) 15 87:=by decide +kernel
  have hfast:StrictAtFast (row 15 87) 15 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 87) 15 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 87) 15 87 hvalid hfast

theorem sr15p88:∀ i ∈ List.range 1,StrictCheckAt 15 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 88) 15 88:=by decide +kernel
  have hfast:StrictAtFast (row 15 88) 15 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 88) 15 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 88) 15 88 hvalid hfast

theorem sr15p89:∀ i ∈ List.range 1,StrictCheckAt 15 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 89) 15 89:=by decide +kernel
  have hfast:StrictAtFast (row 15 89) 15 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 89) 15 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 89) 15 89 hvalid hfast

theorem sr15p90:∀ i ∈ List.range 1,StrictCheckAt 15 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 90) 15 90:=by decide +kernel
  have hfast:StrictAtFast (row 15 90) 15 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 90) 15 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 90) 15 90 hvalid hfast

theorem sr15p91:∀ i ∈ List.range 1,StrictCheckAt 15 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 91) 15 91:=by decide +kernel
  have hfast:StrictAtFast (row 15 91) 15 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 91) 15 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 91) 15 91 hvalid hfast

theorem sr15p92:∀ i ∈ List.range 1,StrictCheckAt 15 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 92) 15 92:=by decide +kernel
  have hfast:StrictAtFast (row 15 92) 15 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 92) 15 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 92) 15 92 hvalid hfast

theorem sr15p93:∀ i ∈ List.range 1,StrictCheckAt 15 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 93) 15 93:=by decide +kernel
  have hfast:StrictAtFast (row 15 93) 15 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 93) 15 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 93) 15 93 hvalid hfast

theorem sr15p94:∀ i ∈ List.range 1,StrictCheckAt 15 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 94) 15 94:=by decide +kernel
  have hfast:StrictAtFast (row 15 94) 15 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 94) 15 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 94) 15 94 hvalid hfast

theorem sr15p95:∀ i ∈ List.range 1,StrictCheckAt 15 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 95) 15 95:=by decide +kernel
  have hfast:StrictAtFast (row 15 95) 15 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 95) 15 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 95) 15 95 hvalid hfast

theorem sr15p96:∀ i ∈ List.range 1,StrictCheckAt 15 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 96) 15 96:=by decide +kernel
  have hfast:StrictAtFast (row 15 96) 15 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 96) 15 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 96) 15 96 hvalid hfast

theorem sr15p97:∀ i ∈ List.range 1,StrictCheckAt 15 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 97) 15 97:=by decide +kernel
  have hfast:StrictAtFast (row 15 97) 15 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 97) 15 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 97) 15 97 hvalid hfast

theorem sr15p98:∀ i ∈ List.range 1,StrictCheckAt 15 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 98) 15 98:=by decide +kernel
  have hfast:StrictAtFast (row 15 98) 15 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 98) 15 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 98) 15 98 hvalid hfast

theorem sr15p99:∀ i ∈ List.range 1,StrictCheckAt 15 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 99) 15 99:=by decide +kernel
  have hfast:StrictAtFast (row 15 99) 15 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 99) 15 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 99) 15 99 hvalid hfast

theorem sr15p100:∀ i ∈ List.range 1,StrictCheckAt 15 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 100) 15 100:=by decide +kernel
  have hfast:StrictAtFast (row 15 100) 15 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 100) 15 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 100) 15 100 hvalid hfast

theorem sr15p101:∀ i ∈ List.range 1,StrictCheckAt 15 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 101) 15 101:=by decide +kernel
  have hfast:StrictAtFast (row 15 101) 15 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 101) 15 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 101) 15 101 hvalid hfast

theorem sr15p102:∀ i ∈ List.range 1,StrictCheckAt 15 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 102) 15 102:=by decide +kernel
  have hfast:StrictAtFast (row 15 102) 15 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 102) 15 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 102) 15 102 hvalid hfast

theorem sr15p103:∀ i ∈ List.range 1,StrictCheckAt 15 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 103) 15 103:=by decide +kernel
  have hfast:StrictAtFast (row 15 103) 15 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 103) 15 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 103) 15 103 hvalid hfast

theorem sr15p104:∀ i ∈ List.range 1,StrictCheckAt 15 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 104) 15 104:=by decide +kernel
  have hfast:StrictAtFast (row 15 104) 15 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 104) 15 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 104) 15 104 hvalid hfast

theorem sr15p105:∀ i ∈ List.range 1,StrictCheckAt 15 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 105) 15 105:=by decide +kernel
  have hfast:StrictAtFast (row 15 105) 15 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 105) 15 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 105) 15 105 hvalid hfast

theorem sr15p106:∀ i ∈ List.range 1,StrictCheckAt 15 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 106) 15 106:=by decide +kernel
  have hfast:StrictAtFast (row 15 106) 15 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 106) 15 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 106) 15 106 hvalid hfast

theorem sr15p107:∀ i ∈ List.range 1,StrictCheckAt 15 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 107) 15 107:=by decide +kernel
  have hfast:StrictAtFast (row 15 107) 15 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 107) 15 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 107) 15 107 hvalid hfast

theorem sr15p108:∀ i ∈ List.range 1,StrictCheckAt 15 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 108) 15 108:=by decide +kernel
  have hfast:StrictAtFast (row 15 108) 15 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 108) 15 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 108) 15 108 hvalid hfast

theorem sr15p109:∀ i ∈ List.range 1,StrictCheckAt 15 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 109) 15 109:=by decide +kernel
  have hfast:StrictAtFast (row 15 109) 15 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 109) 15 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 109) 15 109 hvalid hfast

theorem sr15p110:∀ i ∈ List.range 1,StrictCheckAt 15 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 110) 15 110:=by decide +kernel
  have hfast:StrictAtFast (row 15 110) 15 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 110) 15 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 110) 15 110 hvalid hfast

theorem sr15p111:∀ i ∈ List.range 1,StrictCheckAt 15 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 111) 15 111:=by decide +kernel
  have hfast:StrictAtFast (row 15 111) 15 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 111) 15 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 111) 15 111 hvalid hfast

theorem sr15p112:∀ i ∈ List.range 1,StrictCheckAt 15 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 112) 15 112:=by decide +kernel
  have hfast:StrictAtFast (row 15 112) 15 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 112) 15 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 112) 15 112 hvalid hfast

theorem sr15p113:∀ i ∈ List.range 1,StrictCheckAt 15 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 113) 15 113:=by decide +kernel
  have hfast:StrictAtFast (row 15 113) 15 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 113) 15 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 113) 15 113 hvalid hfast

theorem sr15p114:∀ i ∈ List.range 1,StrictCheckAt 15 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 114) 15 114:=by decide +kernel
  have hfast:StrictAtFast (row 15 114) 15 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 114) 15 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 114) 15 114 hvalid hfast

theorem sr15p115:∀ i ∈ List.range 1,StrictCheckAt 15 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 115) 15 115:=by decide +kernel
  have hfast:StrictAtFast (row 15 115) 15 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 115) 15 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 115) 15 115 hvalid hfast

theorem sr15p116:∀ i ∈ List.range 1,StrictCheckAt 15 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 116) 15 116:=by decide +kernel
  have hfast:StrictAtFast (row 15 116) 15 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 116) 15 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 116) 15 116 hvalid hfast

theorem sr15p117:∀ i ∈ List.range 1,StrictCheckAt 15 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 117) 15 117:=by decide +kernel
  have hfast:StrictAtFast (row 15 117) 15 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 117) 15 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 117) 15 117 hvalid hfast

theorem sr15p118:∀ i ∈ List.range 1,StrictCheckAt 15 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 118) 15 118:=by decide +kernel
  have hfast:StrictAtFast (row 15 118) 15 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 118) 15 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 118) 15 118 hvalid hfast

theorem sr15p119:∀ i ∈ List.range 1,StrictCheckAt 15 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 119) 15 119:=by decide +kernel
  have hfast:StrictAtFast (row 15 119) 15 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 119) 15 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 119) 15 119 hvalid hfast

theorem sr15p120:∀ i ∈ List.range 1,StrictCheckAt 15 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 120) 15 120:=by decide +kernel
  have hfast:StrictAtFast (row 15 120) 15 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 120) 15 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 120) 15 120 hvalid hfast

theorem sr15p121:∀ i ∈ List.range 1,StrictCheckAt 15 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 121) 15 121:=by decide +kernel
  have hfast:StrictAtFast (row 15 121) 15 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 121) 15 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 121) 15 121 hvalid hfast

theorem sr15p122:∀ i ∈ List.range 1,StrictCheckAt 15 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 122) 15 122:=by decide +kernel
  have hfast:StrictAtFast (row 15 122) 15 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 122) 15 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 122) 15 122 hvalid hfast

theorem sr15p123:∀ i ∈ List.range 1,StrictCheckAt 15 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 123) 15 123:=by decide +kernel
  have hfast:StrictAtFast (row 15 123) 15 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 123) 15 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 123) 15 123 hvalid hfast

theorem sr15p124:∀ i ∈ List.range 1,StrictCheckAt 15 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 124) 15 124:=by decide +kernel
  have hfast:StrictAtFast (row 15 124) 15 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 124) 15 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 124) 15 124 hvalid hfast

theorem sr15p125:∀ i ∈ List.range 1,StrictCheckAt 15 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 125) 15 125:=by decide +kernel
  have hfast:StrictAtFast (row 15 125) 15 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 125) 15 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 125) 15 125 hvalid hfast

theorem sr15p126:∀ i ∈ List.range 1,StrictCheckAt 15 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 126) 15 126:=by decide +kernel
  have hfast:StrictAtFast (row 15 126) 15 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 126) 15 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 126) 15 126 hvalid hfast

theorem sr15p127:∀ i ∈ List.range 1,StrictCheckAt 15 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 15 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 15 127) 15 127:=by decide +kernel
  have hfast:StrictAtFast (row 15 127) 15 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 15 127) 15 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 15 127) 15 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
