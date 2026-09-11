import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
