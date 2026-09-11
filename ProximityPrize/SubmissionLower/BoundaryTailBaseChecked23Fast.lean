import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr23p0:∀ i ∈ List.range 8,CorrectAt 23 (0+i):=by decide +kernel

theorem cr23p1:∀ i ∈ List.range 8,CorrectAt 23 (8+i):=by decide +kernel

theorem cr23p2:∀ i ∈ List.range 8,CorrectAt 23 (16+i):=by decide +kernel

theorem cr23p3:∀ i ∈ List.range 8,CorrectAt 23 (24+i):=by decide +kernel

theorem cr23p4:∀ i ∈ List.range 8,CorrectAt 23 (32+i):=by decide +kernel

theorem cr23p5:∀ i ∈ List.range 8,CorrectAt 23 (40+i):=by decide +kernel

theorem cr23p6:∀ i ∈ List.range 8,CorrectAt 23 (48+i):=by decide +kernel

theorem cr23p7:∀ i ∈ List.range 8,CorrectAt 23 (56+i):=by decide +kernel

theorem cr23p8:∀ i ∈ List.range 8,CorrectAt 23 (64+i):=by decide +kernel

theorem cr23p9:∀ i ∈ List.range 8,CorrectAt 23 (72+i):=by decide +kernel

theorem cr23p10:∀ i ∈ List.range 8,CorrectAt 23 (80+i):=by decide +kernel

theorem cr23p11:∀ i ∈ List.range 8,CorrectAt 23 (88+i):=by decide +kernel

theorem cr23p12:∀ i ∈ List.range 8,CorrectAt 23 (96+i):=by decide +kernel

theorem cr23p13:∀ i ∈ List.range 8,CorrectAt 23 (104+i):=by decide +kernel

theorem cr23p14:∀ i ∈ List.range 8,CorrectAt 23 (112+i):=by decide +kernel

theorem sr23p0:∀ i ∈ List.range 1,StrictCheckAt 23 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 0) 23 0:=by decide +kernel
  have hfast:StrictAtFast (row 23 0) 23 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 0) 23 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 0) 23 0 hvalid hfast

theorem sr23p1:∀ i ∈ List.range 1,StrictCheckAt 23 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 1) 23 1:=by decide +kernel
  have hfast:StrictAtFast (row 23 1) 23 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 1) 23 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 1) 23 1 hvalid hfast

theorem sr23p2:∀ i ∈ List.range 1,StrictCheckAt 23 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 2) 23 2:=by decide +kernel
  have hfast:StrictAtFast (row 23 2) 23 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 2) 23 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 2) 23 2 hvalid hfast

theorem sr23p3:∀ i ∈ List.range 1,StrictCheckAt 23 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 3) 23 3:=by decide +kernel
  have hfast:StrictAtFast (row 23 3) 23 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 3) 23 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 3) 23 3 hvalid hfast

theorem sr23p4:∀ i ∈ List.range 1,StrictCheckAt 23 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 4) 23 4:=by decide +kernel
  have hfast:StrictAtFast (row 23 4) 23 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 4) 23 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 4) 23 4 hvalid hfast

theorem sr23p5:∀ i ∈ List.range 1,StrictCheckAt 23 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 5) 23 5:=by decide +kernel
  have hfast:StrictAtFast (row 23 5) 23 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 5) 23 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 5) 23 5 hvalid hfast

theorem sr23p6:∀ i ∈ List.range 1,StrictCheckAt 23 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 6) 23 6:=by decide +kernel
  have hfast:StrictAtFast (row 23 6) 23 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 6) 23 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 6) 23 6 hvalid hfast

theorem sr23p7:∀ i ∈ List.range 1,StrictCheckAt 23 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 7) 23 7:=by decide +kernel
  have hfast:StrictAtFast (row 23 7) 23 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 7) 23 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 7) 23 7 hvalid hfast

theorem sr23p8:∀ i ∈ List.range 1,StrictCheckAt 23 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 8) 23 8:=by decide +kernel
  have hfast:StrictAtFast (row 23 8) 23 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 8) 23 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 8) 23 8 hvalid hfast

theorem sr23p9:∀ i ∈ List.range 1,StrictCheckAt 23 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 9) 23 9:=by decide +kernel
  have hfast:StrictAtFast (row 23 9) 23 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 9) 23 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 9) 23 9 hvalid hfast

theorem sr23p10:∀ i ∈ List.range 1,StrictCheckAt 23 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 10) 23 10:=by decide +kernel
  have hfast:StrictAtFast (row 23 10) 23 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 10) 23 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 10) 23 10 hvalid hfast

theorem sr23p11:∀ i ∈ List.range 1,StrictCheckAt 23 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 11) 23 11:=by decide +kernel
  have hfast:StrictAtFast (row 23 11) 23 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 11) 23 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 11) 23 11 hvalid hfast

theorem sr23p12:∀ i ∈ List.range 1,StrictCheckAt 23 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 12) 23 12:=by decide +kernel
  have hfast:StrictAtFast (row 23 12) 23 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 12) 23 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 12) 23 12 hvalid hfast

theorem sr23p13:∀ i ∈ List.range 1,StrictCheckAt 23 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 13) 23 13:=by decide +kernel
  have hfast:StrictAtFast (row 23 13) 23 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 13) 23 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 13) 23 13 hvalid hfast

theorem sr23p14:∀ i ∈ List.range 1,StrictCheckAt 23 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 14) 23 14:=by decide +kernel
  have hfast:StrictAtFast (row 23 14) 23 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 14) 23 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 14) 23 14 hvalid hfast

theorem sr23p15:∀ i ∈ List.range 1,StrictCheckAt 23 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 15) 23 15:=by decide +kernel
  have hfast:StrictAtFast (row 23 15) 23 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 15) 23 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 15) 23 15 hvalid hfast

theorem sr23p16:∀ i ∈ List.range 1,StrictCheckAt 23 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 16) 23 16:=by decide +kernel
  have hfast:StrictAtFast (row 23 16) 23 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 16) 23 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 16) 23 16 hvalid hfast

theorem sr23p17:∀ i ∈ List.range 1,StrictCheckAt 23 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 17) 23 17:=by decide +kernel
  have hfast:StrictAtFast (row 23 17) 23 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 17) 23 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 17) 23 17 hvalid hfast

theorem sr23p18:∀ i ∈ List.range 1,StrictCheckAt 23 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 18) 23 18:=by decide +kernel
  have hfast:StrictAtFast (row 23 18) 23 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 18) 23 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 18) 23 18 hvalid hfast

theorem sr23p19:∀ i ∈ List.range 1,StrictCheckAt 23 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 19) 23 19:=by decide +kernel
  have hfast:StrictAtFast (row 23 19) 23 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 19) 23 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 19) 23 19 hvalid hfast

theorem sr23p20:∀ i ∈ List.range 1,StrictCheckAt 23 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 20) 23 20:=by decide +kernel
  have hfast:StrictAtFast (row 23 20) 23 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 20) 23 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 20) 23 20 hvalid hfast

theorem sr23p21:∀ i ∈ List.range 1,StrictCheckAt 23 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 21) 23 21:=by decide +kernel
  have hfast:StrictAtFast (row 23 21) 23 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 21) 23 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 21) 23 21 hvalid hfast

theorem sr23p22:∀ i ∈ List.range 1,StrictCheckAt 23 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 22) 23 22:=by decide +kernel
  have hfast:StrictAtFast (row 23 22) 23 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 22) 23 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 22) 23 22 hvalid hfast

theorem sr23p23:∀ i ∈ List.range 1,StrictCheckAt 23 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 23) 23 23:=by decide +kernel
  have hfast:StrictAtFast (row 23 23) 23 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 23) 23 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 23) 23 23 hvalid hfast

theorem sr23p24:∀ i ∈ List.range 1,StrictCheckAt 23 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 24) 23 24:=by decide +kernel
  have hfast:StrictAtFast (row 23 24) 23 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 24) 23 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 24) 23 24 hvalid hfast

theorem sr23p25:∀ i ∈ List.range 1,StrictCheckAt 23 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 25) 23 25:=by decide +kernel
  have hfast:StrictAtFast (row 23 25) 23 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 25) 23 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 25) 23 25 hvalid hfast

theorem sr23p26:∀ i ∈ List.range 1,StrictCheckAt 23 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 26) 23 26:=by decide +kernel
  have hfast:StrictAtFast (row 23 26) 23 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 26) 23 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 26) 23 26 hvalid hfast

theorem sr23p27:∀ i ∈ List.range 1,StrictCheckAt 23 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 27) 23 27:=by decide +kernel
  have hfast:StrictAtFast (row 23 27) 23 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 27) 23 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 27) 23 27 hvalid hfast

theorem sr23p28:∀ i ∈ List.range 1,StrictCheckAt 23 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 28) 23 28:=by decide +kernel
  have hfast:StrictAtFast (row 23 28) 23 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 28) 23 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 28) 23 28 hvalid hfast

theorem sr23p29:∀ i ∈ List.range 1,StrictCheckAt 23 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 29) 23 29:=by decide +kernel
  have hfast:StrictAtFast (row 23 29) 23 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 29) 23 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 29) 23 29 hvalid hfast

theorem sr23p30:∀ i ∈ List.range 1,StrictCheckAt 23 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 30) 23 30:=by decide +kernel
  have hfast:StrictAtFast (row 23 30) 23 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 30) 23 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 30) 23 30 hvalid hfast

theorem sr23p31:∀ i ∈ List.range 1,StrictCheckAt 23 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 31) 23 31:=by decide +kernel
  have hfast:StrictAtFast (row 23 31) 23 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 31) 23 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 31) 23 31 hvalid hfast

theorem sr23p32:∀ i ∈ List.range 1,StrictCheckAt 23 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 32) 23 32:=by decide +kernel
  have hfast:StrictAtFast (row 23 32) 23 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 32) 23 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 32) 23 32 hvalid hfast

theorem sr23p33:∀ i ∈ List.range 1,StrictCheckAt 23 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 33) 23 33:=by decide +kernel
  have hfast:StrictAtFast (row 23 33) 23 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 33) 23 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 33) 23 33 hvalid hfast

theorem sr23p34:∀ i ∈ List.range 1,StrictCheckAt 23 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 34) 23 34:=by decide +kernel
  have hfast:StrictAtFast (row 23 34) 23 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 34) 23 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 34) 23 34 hvalid hfast

theorem sr23p35:∀ i ∈ List.range 1,StrictCheckAt 23 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 35) 23 35:=by decide +kernel
  have hfast:StrictAtFast (row 23 35) 23 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 35) 23 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 35) 23 35 hvalid hfast

theorem sr23p36:∀ i ∈ List.range 1,StrictCheckAt 23 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 36) 23 36:=by decide +kernel
  have hfast:StrictAtFast (row 23 36) 23 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 36) 23 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 36) 23 36 hvalid hfast

theorem sr23p37:∀ i ∈ List.range 1,StrictCheckAt 23 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 37) 23 37:=by decide +kernel
  have hfast:StrictAtFast (row 23 37) 23 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 37) 23 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 37) 23 37 hvalid hfast

theorem sr23p38:∀ i ∈ List.range 1,StrictCheckAt 23 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 38) 23 38:=by decide +kernel
  have hfast:StrictAtFast (row 23 38) 23 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 38) 23 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 38) 23 38 hvalid hfast

theorem sr23p39:∀ i ∈ List.range 1,StrictCheckAt 23 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 39) 23 39:=by decide +kernel
  have hfast:StrictAtFast (row 23 39) 23 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 39) 23 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 39) 23 39 hvalid hfast

theorem sr23p40:∀ i ∈ List.range 1,StrictCheckAt 23 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 40) 23 40:=by decide +kernel
  have hfast:StrictAtFast (row 23 40) 23 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 40) 23 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 40) 23 40 hvalid hfast

theorem sr23p41:∀ i ∈ List.range 1,StrictCheckAt 23 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 41) 23 41:=by decide +kernel
  have hfast:StrictAtFast (row 23 41) 23 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 41) 23 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 41) 23 41 hvalid hfast

theorem sr23p42:∀ i ∈ List.range 1,StrictCheckAt 23 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 42) 23 42:=by decide +kernel
  have hfast:StrictAtFast (row 23 42) 23 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 42) 23 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 42) 23 42 hvalid hfast

theorem sr23p43:∀ i ∈ List.range 1,StrictCheckAt 23 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 43) 23 43:=by decide +kernel
  have hfast:StrictAtFast (row 23 43) 23 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 43) 23 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 43) 23 43 hvalid hfast

theorem sr23p44:∀ i ∈ List.range 1,StrictCheckAt 23 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 44) 23 44:=by decide +kernel
  have hfast:StrictAtFast (row 23 44) 23 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 44) 23 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 44) 23 44 hvalid hfast

theorem sr23p45:∀ i ∈ List.range 1,StrictCheckAt 23 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 45) 23 45:=by decide +kernel
  have hfast:StrictAtFast (row 23 45) 23 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 45) 23 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 45) 23 45 hvalid hfast

theorem sr23p46:∀ i ∈ List.range 1,StrictCheckAt 23 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 46) 23 46:=by decide +kernel
  have hfast:StrictAtFast (row 23 46) 23 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 46) 23 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 46) 23 46 hvalid hfast

theorem sr23p47:∀ i ∈ List.range 1,StrictCheckAt 23 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 47) 23 47:=by decide +kernel
  have hfast:StrictAtFast (row 23 47) 23 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 47) 23 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 47) 23 47 hvalid hfast

theorem sr23p48:∀ i ∈ List.range 1,StrictCheckAt 23 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 48) 23 48:=by decide +kernel
  have hfast:StrictAtFast (row 23 48) 23 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 48) 23 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 48) 23 48 hvalid hfast

theorem sr23p49:∀ i ∈ List.range 1,StrictCheckAt 23 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 49) 23 49:=by decide +kernel
  have hfast:StrictAtFast (row 23 49) 23 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 49) 23 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 49) 23 49 hvalid hfast

theorem sr23p50:∀ i ∈ List.range 1,StrictCheckAt 23 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 50) 23 50:=by decide +kernel
  have hfast:StrictAtFast (row 23 50) 23 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 50) 23 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 50) 23 50 hvalid hfast

theorem sr23p51:∀ i ∈ List.range 1,StrictCheckAt 23 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 51) 23 51:=by decide +kernel
  have hfast:StrictAtFast (row 23 51) 23 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 51) 23 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 51) 23 51 hvalid hfast

theorem sr23p52:∀ i ∈ List.range 1,StrictCheckAt 23 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 52) 23 52:=by decide +kernel
  have hfast:StrictAtFast (row 23 52) 23 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 52) 23 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 52) 23 52 hvalid hfast

theorem sr23p53:∀ i ∈ List.range 1,StrictCheckAt 23 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 53) 23 53:=by decide +kernel
  have hfast:StrictAtFast (row 23 53) 23 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 53) 23 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 53) 23 53 hvalid hfast

theorem sr23p54:∀ i ∈ List.range 1,StrictCheckAt 23 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 54) 23 54:=by decide +kernel
  have hfast:StrictAtFast (row 23 54) 23 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 54) 23 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 54) 23 54 hvalid hfast

theorem sr23p55:∀ i ∈ List.range 1,StrictCheckAt 23 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 55) 23 55:=by decide +kernel
  have hfast:StrictAtFast (row 23 55) 23 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 55) 23 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 55) 23 55 hvalid hfast

theorem sr23p56:∀ i ∈ List.range 1,StrictCheckAt 23 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 56) 23 56:=by decide +kernel
  have hfast:StrictAtFast (row 23 56) 23 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 56) 23 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 56) 23 56 hvalid hfast

theorem sr23p57:∀ i ∈ List.range 1,StrictCheckAt 23 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 57) 23 57:=by decide +kernel
  have hfast:StrictAtFast (row 23 57) 23 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 57) 23 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 57) 23 57 hvalid hfast

theorem sr23p58:∀ i ∈ List.range 1,StrictCheckAt 23 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 58) 23 58:=by decide +kernel
  have hfast:StrictAtFast (row 23 58) 23 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 58) 23 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 58) 23 58 hvalid hfast

theorem sr23p59:∀ i ∈ List.range 1,StrictCheckAt 23 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 59) 23 59:=by decide +kernel
  have hfast:StrictAtFast (row 23 59) 23 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 59) 23 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 59) 23 59 hvalid hfast

theorem sr23p60:∀ i ∈ List.range 1,StrictCheckAt 23 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 60) 23 60:=by decide +kernel
  have hfast:StrictAtFast (row 23 60) 23 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 60) 23 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 60) 23 60 hvalid hfast

theorem sr23p61:∀ i ∈ List.range 1,StrictCheckAt 23 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 61) 23 61:=by decide +kernel
  have hfast:StrictAtFast (row 23 61) 23 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 61) 23 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 61) 23 61 hvalid hfast

theorem sr23p62:∀ i ∈ List.range 1,StrictCheckAt 23 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 62) 23 62:=by decide +kernel
  have hfast:StrictAtFast (row 23 62) 23 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 62) 23 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 62) 23 62 hvalid hfast

theorem sr23p63:∀ i ∈ List.range 1,StrictCheckAt 23 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 63) 23 63:=by decide +kernel
  have hfast:StrictAtFast (row 23 63) 23 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 63) 23 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 63) 23 63 hvalid hfast

theorem sr23p64:∀ i ∈ List.range 1,StrictCheckAt 23 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 64) 23 64:=by decide +kernel
  have hfast:StrictAtFast (row 23 64) 23 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 64) 23 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 64) 23 64 hvalid hfast

theorem sr23p65:∀ i ∈ List.range 1,StrictCheckAt 23 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 65) 23 65:=by decide +kernel
  have hfast:StrictAtFast (row 23 65) 23 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 65) 23 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 65) 23 65 hvalid hfast

theorem sr23p66:∀ i ∈ List.range 1,StrictCheckAt 23 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 66) 23 66:=by decide +kernel
  have hfast:StrictAtFast (row 23 66) 23 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 66) 23 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 66) 23 66 hvalid hfast

theorem sr23p67:∀ i ∈ List.range 1,StrictCheckAt 23 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 67) 23 67:=by decide +kernel
  have hfast:StrictAtFast (row 23 67) 23 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 67) 23 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 67) 23 67 hvalid hfast

theorem sr23p68:∀ i ∈ List.range 1,StrictCheckAt 23 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 68) 23 68:=by decide +kernel
  have hfast:StrictAtFast (row 23 68) 23 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 68) 23 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 68) 23 68 hvalid hfast

theorem sr23p69:∀ i ∈ List.range 1,StrictCheckAt 23 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 69) 23 69:=by decide +kernel
  have hfast:StrictAtFast (row 23 69) 23 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 69) 23 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 69) 23 69 hvalid hfast

theorem sr23p70:∀ i ∈ List.range 1,StrictCheckAt 23 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 70) 23 70:=by decide +kernel
  have hfast:StrictAtFast (row 23 70) 23 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 70) 23 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 70) 23 70 hvalid hfast

theorem sr23p71:∀ i ∈ List.range 1,StrictCheckAt 23 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 71) 23 71:=by decide +kernel
  have hfast:StrictAtFast (row 23 71) 23 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 71) 23 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 71) 23 71 hvalid hfast

theorem sr23p72:∀ i ∈ List.range 1,StrictCheckAt 23 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 72) 23 72:=by decide +kernel
  have hfast:StrictAtFast (row 23 72) 23 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 72) 23 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 72) 23 72 hvalid hfast

theorem sr23p73:∀ i ∈ List.range 1,StrictCheckAt 23 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 73) 23 73:=by decide +kernel
  have hfast:StrictAtFast (row 23 73) 23 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 73) 23 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 73) 23 73 hvalid hfast

theorem sr23p74:∀ i ∈ List.range 1,StrictCheckAt 23 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 74) 23 74:=by decide +kernel
  have hfast:StrictAtFast (row 23 74) 23 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 74) 23 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 74) 23 74 hvalid hfast

theorem sr23p75:∀ i ∈ List.range 1,StrictCheckAt 23 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 75) 23 75:=by decide +kernel
  have hfast:StrictAtFast (row 23 75) 23 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 75) 23 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 75) 23 75 hvalid hfast

theorem sr23p76:∀ i ∈ List.range 1,StrictCheckAt 23 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 76) 23 76:=by decide +kernel
  have hfast:StrictAtFast (row 23 76) 23 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 76) 23 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 76) 23 76 hvalid hfast

theorem sr23p77:∀ i ∈ List.range 1,StrictCheckAt 23 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 77) 23 77:=by decide +kernel
  have hfast:StrictAtFast (row 23 77) 23 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 77) 23 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 77) 23 77 hvalid hfast

theorem sr23p78:∀ i ∈ List.range 1,StrictCheckAt 23 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 78) 23 78:=by decide +kernel
  have hfast:StrictAtFast (row 23 78) 23 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 78) 23 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 78) 23 78 hvalid hfast

theorem sr23p79:∀ i ∈ List.range 1,StrictCheckAt 23 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 79) 23 79:=by decide +kernel
  have hfast:StrictAtFast (row 23 79) 23 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 79) 23 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 79) 23 79 hvalid hfast

theorem sr23p80:∀ i ∈ List.range 1,StrictCheckAt 23 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 80) 23 80:=by decide +kernel
  have hfast:StrictAtFast (row 23 80) 23 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 80) 23 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 80) 23 80 hvalid hfast

theorem sr23p81:∀ i ∈ List.range 1,StrictCheckAt 23 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 81) 23 81:=by decide +kernel
  have hfast:StrictAtFast (row 23 81) 23 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 81) 23 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 81) 23 81 hvalid hfast

theorem sr23p82:∀ i ∈ List.range 1,StrictCheckAt 23 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 82) 23 82:=by decide +kernel
  have hfast:StrictAtFast (row 23 82) 23 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 82) 23 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 82) 23 82 hvalid hfast

theorem sr23p83:∀ i ∈ List.range 1,StrictCheckAt 23 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 83) 23 83:=by decide +kernel
  have hfast:StrictAtFast (row 23 83) 23 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 83) 23 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 83) 23 83 hvalid hfast

theorem sr23p84:∀ i ∈ List.range 1,StrictCheckAt 23 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 84) 23 84:=by decide +kernel
  have hfast:StrictAtFast (row 23 84) 23 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 84) 23 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 84) 23 84 hvalid hfast

theorem sr23p85:∀ i ∈ List.range 1,StrictCheckAt 23 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 85) 23 85:=by decide +kernel
  have hfast:StrictAtFast (row 23 85) 23 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 85) 23 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 85) 23 85 hvalid hfast

theorem sr23p86:∀ i ∈ List.range 1,StrictCheckAt 23 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 86) 23 86:=by decide +kernel
  have hfast:StrictAtFast (row 23 86) 23 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 86) 23 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 86) 23 86 hvalid hfast

theorem sr23p87:∀ i ∈ List.range 1,StrictCheckAt 23 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 87) 23 87:=by decide +kernel
  have hfast:StrictAtFast (row 23 87) 23 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 87) 23 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 87) 23 87 hvalid hfast

theorem sr23p88:∀ i ∈ List.range 1,StrictCheckAt 23 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 88) 23 88:=by decide +kernel
  have hfast:StrictAtFast (row 23 88) 23 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 88) 23 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 88) 23 88 hvalid hfast

theorem sr23p89:∀ i ∈ List.range 1,StrictCheckAt 23 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 89) 23 89:=by decide +kernel
  have hfast:StrictAtFast (row 23 89) 23 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 89) 23 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 89) 23 89 hvalid hfast

theorem sr23p90:∀ i ∈ List.range 1,StrictCheckAt 23 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 90) 23 90:=by decide +kernel
  have hfast:StrictAtFast (row 23 90) 23 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 90) 23 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 90) 23 90 hvalid hfast

theorem sr23p91:∀ i ∈ List.range 1,StrictCheckAt 23 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 91) 23 91:=by decide +kernel
  have hfast:StrictAtFast (row 23 91) 23 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 91) 23 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 91) 23 91 hvalid hfast

theorem sr23p92:∀ i ∈ List.range 1,StrictCheckAt 23 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 92) 23 92:=by decide +kernel
  have hfast:StrictAtFast (row 23 92) 23 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 92) 23 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 92) 23 92 hvalid hfast

theorem sr23p93:∀ i ∈ List.range 1,StrictCheckAt 23 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 93) 23 93:=by decide +kernel
  have hfast:StrictAtFast (row 23 93) 23 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 93) 23 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 93) 23 93 hvalid hfast

theorem sr23p94:∀ i ∈ List.range 1,StrictCheckAt 23 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 94) 23 94:=by decide +kernel
  have hfast:StrictAtFast (row 23 94) 23 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 94) 23 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 94) 23 94 hvalid hfast

theorem sr23p95:∀ i ∈ List.range 1,StrictCheckAt 23 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 95) 23 95:=by decide +kernel
  have hfast:StrictAtFast (row 23 95) 23 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 95) 23 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 95) 23 95 hvalid hfast

theorem sr23p96:∀ i ∈ List.range 1,StrictCheckAt 23 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 96) 23 96:=by decide +kernel
  have hfast:StrictAtFast (row 23 96) 23 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 96) 23 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 96) 23 96 hvalid hfast

theorem sr23p97:∀ i ∈ List.range 1,StrictCheckAt 23 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 97) 23 97:=by decide +kernel
  have hfast:StrictAtFast (row 23 97) 23 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 97) 23 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 97) 23 97 hvalid hfast

theorem sr23p98:∀ i ∈ List.range 1,StrictCheckAt 23 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 98) 23 98:=by decide +kernel
  have hfast:StrictAtFast (row 23 98) 23 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 98) 23 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 98) 23 98 hvalid hfast

theorem sr23p99:∀ i ∈ List.range 1,StrictCheckAt 23 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 99) 23 99:=by decide +kernel
  have hfast:StrictAtFast (row 23 99) 23 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 99) 23 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 99) 23 99 hvalid hfast

theorem sr23p100:∀ i ∈ List.range 1,StrictCheckAt 23 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 100) 23 100:=by decide +kernel
  have hfast:StrictAtFast (row 23 100) 23 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 100) 23 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 100) 23 100 hvalid hfast

theorem sr23p101:∀ i ∈ List.range 1,StrictCheckAt 23 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 101) 23 101:=by decide +kernel
  have hfast:StrictAtFast (row 23 101) 23 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 101) 23 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 101) 23 101 hvalid hfast

theorem sr23p102:∀ i ∈ List.range 1,StrictCheckAt 23 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 102) 23 102:=by decide +kernel
  have hfast:StrictAtFast (row 23 102) 23 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 102) 23 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 102) 23 102 hvalid hfast

theorem sr23p103:∀ i ∈ List.range 1,StrictCheckAt 23 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 103) 23 103:=by decide +kernel
  have hfast:StrictAtFast (row 23 103) 23 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 103) 23 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 103) 23 103 hvalid hfast

theorem sr23p104:∀ i ∈ List.range 1,StrictCheckAt 23 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 104) 23 104:=by decide +kernel
  have hfast:StrictAtFast (row 23 104) 23 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 104) 23 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 104) 23 104 hvalid hfast

theorem sr23p105:∀ i ∈ List.range 1,StrictCheckAt 23 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 105) 23 105:=by decide +kernel
  have hfast:StrictAtFast (row 23 105) 23 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 105) 23 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 105) 23 105 hvalid hfast

theorem sr23p106:∀ i ∈ List.range 1,StrictCheckAt 23 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 106) 23 106:=by decide +kernel
  have hfast:StrictAtFast (row 23 106) 23 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 106) 23 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 106) 23 106 hvalid hfast

theorem sr23p107:∀ i ∈ List.range 1,StrictCheckAt 23 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 107) 23 107:=by decide +kernel
  have hfast:StrictAtFast (row 23 107) 23 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 107) 23 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 107) 23 107 hvalid hfast

theorem sr23p108:∀ i ∈ List.range 1,StrictCheckAt 23 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 108) 23 108:=by decide +kernel
  have hfast:StrictAtFast (row 23 108) 23 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 108) 23 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 108) 23 108 hvalid hfast

theorem sr23p109:∀ i ∈ List.range 1,StrictCheckAt 23 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 109) 23 109:=by decide +kernel
  have hfast:StrictAtFast (row 23 109) 23 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 109) 23 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 109) 23 109 hvalid hfast

theorem sr23p110:∀ i ∈ List.range 1,StrictCheckAt 23 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 110) 23 110:=by decide +kernel
  have hfast:StrictAtFast (row 23 110) 23 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 110) 23 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 110) 23 110 hvalid hfast

theorem sr23p111:∀ i ∈ List.range 1,StrictCheckAt 23 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 111) 23 111:=by decide +kernel
  have hfast:StrictAtFast (row 23 111) 23 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 111) 23 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 111) 23 111 hvalid hfast

theorem sr23p112:∀ i ∈ List.range 1,StrictCheckAt 23 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 112) 23 112:=by decide +kernel
  have hfast:StrictAtFast (row 23 112) 23 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 112) 23 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 112) 23 112 hvalid hfast

theorem sr23p113:∀ i ∈ List.range 1,StrictCheckAt 23 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 113) 23 113:=by decide +kernel
  have hfast:StrictAtFast (row 23 113) 23 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 113) 23 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 113) 23 113 hvalid hfast

theorem sr23p114:∀ i ∈ List.range 1,StrictCheckAt 23 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 114) 23 114:=by decide +kernel
  have hfast:StrictAtFast (row 23 114) 23 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 114) 23 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 114) 23 114 hvalid hfast

theorem sr23p115:∀ i ∈ List.range 1,StrictCheckAt 23 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 115) 23 115:=by decide +kernel
  have hfast:StrictAtFast (row 23 115) 23 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 115) 23 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 115) 23 115 hvalid hfast

theorem sr23p116:∀ i ∈ List.range 1,StrictCheckAt 23 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 116) 23 116:=by decide +kernel
  have hfast:StrictAtFast (row 23 116) 23 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 116) 23 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 116) 23 116 hvalid hfast

theorem sr23p117:∀ i ∈ List.range 1,StrictCheckAt 23 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 117) 23 117:=by decide +kernel
  have hfast:StrictAtFast (row 23 117) 23 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 117) 23 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 117) 23 117 hvalid hfast

theorem sr23p118:∀ i ∈ List.range 1,StrictCheckAt 23 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 118) 23 118:=by decide +kernel
  have hfast:StrictAtFast (row 23 118) 23 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 118) 23 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 118) 23 118 hvalid hfast

theorem sr23p119:∀ i ∈ List.range 1,StrictCheckAt 23 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 23 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 23 119) 23 119:=by decide +kernel
  have hfast:StrictAtFast (row 23 119) 23 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 23 119) 23 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 23 119) 23 119 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
