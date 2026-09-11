import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr26p0:∀ i ∈ List.range 8,CorrectAt 26 (0+i):=by decide +kernel

theorem cr26p1:∀ i ∈ List.range 8,CorrectAt 26 (8+i):=by decide +kernel

theorem cr26p2:∀ i ∈ List.range 8,CorrectAt 26 (16+i):=by decide +kernel

theorem cr26p3:∀ i ∈ List.range 8,CorrectAt 26 (24+i):=by decide +kernel

theorem cr26p4:∀ i ∈ List.range 8,CorrectAt 26 (32+i):=by decide +kernel

theorem cr26p5:∀ i ∈ List.range 8,CorrectAt 26 (40+i):=by decide +kernel

theorem cr26p6:∀ i ∈ List.range 8,CorrectAt 26 (48+i):=by decide +kernel

theorem cr26p7:∀ i ∈ List.range 8,CorrectAt 26 (56+i):=by decide +kernel

theorem cr26p8:∀ i ∈ List.range 8,CorrectAt 26 (64+i):=by decide +kernel

theorem cr26p9:∀ i ∈ List.range 8,CorrectAt 26 (72+i):=by decide +kernel

theorem cr26p10:∀ i ∈ List.range 8,CorrectAt 26 (80+i):=by decide +kernel

theorem cr26p11:∀ i ∈ List.range 8,CorrectAt 26 (88+i):=by decide +kernel

theorem cr26p12:∀ i ∈ List.range 8,CorrectAt 26 (96+i):=by decide +kernel

theorem cr26p13:∀ i ∈ List.range 8,CorrectAt 26 (104+i):=by decide +kernel

theorem cr26p14:∀ i ∈ List.range 5,CorrectAt 26 (112+i):=by decide +kernel

theorem sr26p0:∀ i ∈ List.range 1,StrictCheckAt 26 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 0) 26 0:=by decide +kernel
  have hfast:StrictAtFast (row 26 0) 26 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 0) 26 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 0) 26 0 hvalid hfast

theorem sr26p1:∀ i ∈ List.range 1,StrictCheckAt 26 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 1) 26 1:=by decide +kernel
  have hfast:StrictAtFast (row 26 1) 26 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 1) 26 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 1) 26 1 hvalid hfast

theorem sr26p2:∀ i ∈ List.range 1,StrictCheckAt 26 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 2) 26 2:=by decide +kernel
  have hfast:StrictAtFast (row 26 2) 26 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 2) 26 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 2) 26 2 hvalid hfast

theorem sr26p3:∀ i ∈ List.range 1,StrictCheckAt 26 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 3) 26 3:=by decide +kernel
  have hfast:StrictAtFast (row 26 3) 26 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 3) 26 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 3) 26 3 hvalid hfast

theorem sr26p4:∀ i ∈ List.range 1,StrictCheckAt 26 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 4) 26 4:=by decide +kernel
  have hfast:StrictAtFast (row 26 4) 26 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 4) 26 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 4) 26 4 hvalid hfast

theorem sr26p5:∀ i ∈ List.range 1,StrictCheckAt 26 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 5) 26 5:=by decide +kernel
  have hfast:StrictAtFast (row 26 5) 26 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 5) 26 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 5) 26 5 hvalid hfast

theorem sr26p6:∀ i ∈ List.range 1,StrictCheckAt 26 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 6) 26 6:=by decide +kernel
  have hfast:StrictAtFast (row 26 6) 26 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 6) 26 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 6) 26 6 hvalid hfast

theorem sr26p7:∀ i ∈ List.range 1,StrictCheckAt 26 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 7) 26 7:=by decide +kernel
  have hfast:StrictAtFast (row 26 7) 26 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 7) 26 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 7) 26 7 hvalid hfast

theorem sr26p8:∀ i ∈ List.range 1,StrictCheckAt 26 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 8) 26 8:=by decide +kernel
  have hfast:StrictAtFast (row 26 8) 26 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 8) 26 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 8) 26 8 hvalid hfast

theorem sr26p9:∀ i ∈ List.range 1,StrictCheckAt 26 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 9) 26 9:=by decide +kernel
  have hfast:StrictAtFast (row 26 9) 26 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 9) 26 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 9) 26 9 hvalid hfast

theorem sr26p10:∀ i ∈ List.range 1,StrictCheckAt 26 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 10) 26 10:=by decide +kernel
  have hfast:StrictAtFast (row 26 10) 26 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 10) 26 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 10) 26 10 hvalid hfast

theorem sr26p11:∀ i ∈ List.range 1,StrictCheckAt 26 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 11) 26 11:=by decide +kernel
  have hfast:StrictAtFast (row 26 11) 26 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 11) 26 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 11) 26 11 hvalid hfast

theorem sr26p12:∀ i ∈ List.range 1,StrictCheckAt 26 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 12) 26 12:=by decide +kernel
  have hfast:StrictAtFast (row 26 12) 26 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 12) 26 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 12) 26 12 hvalid hfast

theorem sr26p13:∀ i ∈ List.range 1,StrictCheckAt 26 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 13) 26 13:=by decide +kernel
  have hfast:StrictAtFast (row 26 13) 26 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 13) 26 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 13) 26 13 hvalid hfast

theorem sr26p14:∀ i ∈ List.range 1,StrictCheckAt 26 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 14) 26 14:=by decide +kernel
  have hfast:StrictAtFast (row 26 14) 26 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 14) 26 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 14) 26 14 hvalid hfast

theorem sr26p15:∀ i ∈ List.range 1,StrictCheckAt 26 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 15) 26 15:=by decide +kernel
  have hfast:StrictAtFast (row 26 15) 26 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 15) 26 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 15) 26 15 hvalid hfast

theorem sr26p16:∀ i ∈ List.range 1,StrictCheckAt 26 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 16) 26 16:=by decide +kernel
  have hfast:StrictAtFast (row 26 16) 26 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 16) 26 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 16) 26 16 hvalid hfast

theorem sr26p17:∀ i ∈ List.range 1,StrictCheckAt 26 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 17) 26 17:=by decide +kernel
  have hfast:StrictAtFast (row 26 17) 26 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 17) 26 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 17) 26 17 hvalid hfast

theorem sr26p18:∀ i ∈ List.range 1,StrictCheckAt 26 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 18) 26 18:=by decide +kernel
  have hfast:StrictAtFast (row 26 18) 26 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 18) 26 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 18) 26 18 hvalid hfast

theorem sr26p19:∀ i ∈ List.range 1,StrictCheckAt 26 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 19) 26 19:=by decide +kernel
  have hfast:StrictAtFast (row 26 19) 26 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 19) 26 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 19) 26 19 hvalid hfast

theorem sr26p20:∀ i ∈ List.range 1,StrictCheckAt 26 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 20) 26 20:=by decide +kernel
  have hfast:StrictAtFast (row 26 20) 26 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 20) 26 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 20) 26 20 hvalid hfast

theorem sr26p21:∀ i ∈ List.range 1,StrictCheckAt 26 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 21) 26 21:=by decide +kernel
  have hfast:StrictAtFast (row 26 21) 26 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 21) 26 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 21) 26 21 hvalid hfast

theorem sr26p22:∀ i ∈ List.range 1,StrictCheckAt 26 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 22) 26 22:=by decide +kernel
  have hfast:StrictAtFast (row 26 22) 26 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 22) 26 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 22) 26 22 hvalid hfast

theorem sr26p23:∀ i ∈ List.range 1,StrictCheckAt 26 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 23) 26 23:=by decide +kernel
  have hfast:StrictAtFast (row 26 23) 26 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 23) 26 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 23) 26 23 hvalid hfast

theorem sr26p24:∀ i ∈ List.range 1,StrictCheckAt 26 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 24) 26 24:=by decide +kernel
  have hfast:StrictAtFast (row 26 24) 26 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 24) 26 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 24) 26 24 hvalid hfast

theorem sr26p25:∀ i ∈ List.range 1,StrictCheckAt 26 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 25) 26 25:=by decide +kernel
  have hfast:StrictAtFast (row 26 25) 26 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 25) 26 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 25) 26 25 hvalid hfast

theorem sr26p26:∀ i ∈ List.range 1,StrictCheckAt 26 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 26) 26 26:=by decide +kernel
  have hfast:StrictAtFast (row 26 26) 26 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 26) 26 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 26) 26 26 hvalid hfast

theorem sr26p27:∀ i ∈ List.range 1,StrictCheckAt 26 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 27) 26 27:=by decide +kernel
  have hfast:StrictAtFast (row 26 27) 26 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 27) 26 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 27) 26 27 hvalid hfast

theorem sr26p28:∀ i ∈ List.range 1,StrictCheckAt 26 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 28) 26 28:=by decide +kernel
  have hfast:StrictAtFast (row 26 28) 26 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 28) 26 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 28) 26 28 hvalid hfast

theorem sr26p29:∀ i ∈ List.range 1,StrictCheckAt 26 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 29) 26 29:=by decide +kernel
  have hfast:StrictAtFast (row 26 29) 26 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 29) 26 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 29) 26 29 hvalid hfast

theorem sr26p30:∀ i ∈ List.range 1,StrictCheckAt 26 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 30) 26 30:=by decide +kernel
  have hfast:StrictAtFast (row 26 30) 26 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 30) 26 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 30) 26 30 hvalid hfast

theorem sr26p31:∀ i ∈ List.range 1,StrictCheckAt 26 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 31) 26 31:=by decide +kernel
  have hfast:StrictAtFast (row 26 31) 26 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 31) 26 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 31) 26 31 hvalid hfast

theorem sr26p32:∀ i ∈ List.range 1,StrictCheckAt 26 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 32) 26 32:=by decide +kernel
  have hfast:StrictAtFast (row 26 32) 26 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 32) 26 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 32) 26 32 hvalid hfast

theorem sr26p33:∀ i ∈ List.range 1,StrictCheckAt 26 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 33) 26 33:=by decide +kernel
  have hfast:StrictAtFast (row 26 33) 26 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 33) 26 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 33) 26 33 hvalid hfast

theorem sr26p34:∀ i ∈ List.range 1,StrictCheckAt 26 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 34) 26 34:=by decide +kernel
  have hfast:StrictAtFast (row 26 34) 26 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 34) 26 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 34) 26 34 hvalid hfast

theorem sr26p35:∀ i ∈ List.range 1,StrictCheckAt 26 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 35) 26 35:=by decide +kernel
  have hfast:StrictAtFast (row 26 35) 26 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 35) 26 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 35) 26 35 hvalid hfast

theorem sr26p36:∀ i ∈ List.range 1,StrictCheckAt 26 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 36) 26 36:=by decide +kernel
  have hfast:StrictAtFast (row 26 36) 26 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 36) 26 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 36) 26 36 hvalid hfast

theorem sr26p37:∀ i ∈ List.range 1,StrictCheckAt 26 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 37) 26 37:=by decide +kernel
  have hfast:StrictAtFast (row 26 37) 26 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 37) 26 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 37) 26 37 hvalid hfast

theorem sr26p38:∀ i ∈ List.range 1,StrictCheckAt 26 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 38) 26 38:=by decide +kernel
  have hfast:StrictAtFast (row 26 38) 26 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 38) 26 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 38) 26 38 hvalid hfast

theorem sr26p39:∀ i ∈ List.range 1,StrictCheckAt 26 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 39) 26 39:=by decide +kernel
  have hfast:StrictAtFast (row 26 39) 26 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 39) 26 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 39) 26 39 hvalid hfast

theorem sr26p40:∀ i ∈ List.range 1,StrictCheckAt 26 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 40) 26 40:=by decide +kernel
  have hfast:StrictAtFast (row 26 40) 26 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 40) 26 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 40) 26 40 hvalid hfast

theorem sr26p41:∀ i ∈ List.range 1,StrictCheckAt 26 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 41) 26 41:=by decide +kernel
  have hfast:StrictAtFast (row 26 41) 26 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 41) 26 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 41) 26 41 hvalid hfast

theorem sr26p42:∀ i ∈ List.range 1,StrictCheckAt 26 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 42) 26 42:=by decide +kernel
  have hfast:StrictAtFast (row 26 42) 26 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 42) 26 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 42) 26 42 hvalid hfast

theorem sr26p43:∀ i ∈ List.range 1,StrictCheckAt 26 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 43) 26 43:=by decide +kernel
  have hfast:StrictAtFast (row 26 43) 26 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 43) 26 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 43) 26 43 hvalid hfast

theorem sr26p44:∀ i ∈ List.range 1,StrictCheckAt 26 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 44) 26 44:=by decide +kernel
  have hfast:StrictAtFast (row 26 44) 26 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 44) 26 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 44) 26 44 hvalid hfast

theorem sr26p45:∀ i ∈ List.range 1,StrictCheckAt 26 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 45) 26 45:=by decide +kernel
  have hfast:StrictAtFast (row 26 45) 26 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 45) 26 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 45) 26 45 hvalid hfast

theorem sr26p46:∀ i ∈ List.range 1,StrictCheckAt 26 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 46) 26 46:=by decide +kernel
  have hfast:StrictAtFast (row 26 46) 26 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 46) 26 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 46) 26 46 hvalid hfast

theorem sr26p47:∀ i ∈ List.range 1,StrictCheckAt 26 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 47) 26 47:=by decide +kernel
  have hfast:StrictAtFast (row 26 47) 26 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 47) 26 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 47) 26 47 hvalid hfast

theorem sr26p48:∀ i ∈ List.range 1,StrictCheckAt 26 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 48) 26 48:=by decide +kernel
  have hfast:StrictAtFast (row 26 48) 26 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 48) 26 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 48) 26 48 hvalid hfast

theorem sr26p49:∀ i ∈ List.range 1,StrictCheckAt 26 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 49) 26 49:=by decide +kernel
  have hfast:StrictAtFast (row 26 49) 26 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 49) 26 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 49) 26 49 hvalid hfast

theorem sr26p50:∀ i ∈ List.range 1,StrictCheckAt 26 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 50) 26 50:=by decide +kernel
  have hfast:StrictAtFast (row 26 50) 26 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 50) 26 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 50) 26 50 hvalid hfast

theorem sr26p51:∀ i ∈ List.range 1,StrictCheckAt 26 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 51) 26 51:=by decide +kernel
  have hfast:StrictAtFast (row 26 51) 26 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 51) 26 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 51) 26 51 hvalid hfast

theorem sr26p52:∀ i ∈ List.range 1,StrictCheckAt 26 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 52) 26 52:=by decide +kernel
  have hfast:StrictAtFast (row 26 52) 26 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 52) 26 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 52) 26 52 hvalid hfast

theorem sr26p53:∀ i ∈ List.range 1,StrictCheckAt 26 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 53) 26 53:=by decide +kernel
  have hfast:StrictAtFast (row 26 53) 26 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 53) 26 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 53) 26 53 hvalid hfast

theorem sr26p54:∀ i ∈ List.range 1,StrictCheckAt 26 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 54) 26 54:=by decide +kernel
  have hfast:StrictAtFast (row 26 54) 26 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 54) 26 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 54) 26 54 hvalid hfast

theorem sr26p55:∀ i ∈ List.range 1,StrictCheckAt 26 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 55) 26 55:=by decide +kernel
  have hfast:StrictAtFast (row 26 55) 26 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 55) 26 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 55) 26 55 hvalid hfast

theorem sr26p56:∀ i ∈ List.range 1,StrictCheckAt 26 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 56) 26 56:=by decide +kernel
  have hfast:StrictAtFast (row 26 56) 26 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 56) 26 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 56) 26 56 hvalid hfast

theorem sr26p57:∀ i ∈ List.range 1,StrictCheckAt 26 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 57) 26 57:=by decide +kernel
  have hfast:StrictAtFast (row 26 57) 26 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 57) 26 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 57) 26 57 hvalid hfast

theorem sr26p58:∀ i ∈ List.range 1,StrictCheckAt 26 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 58) 26 58:=by decide +kernel
  have hfast:StrictAtFast (row 26 58) 26 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 58) 26 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 58) 26 58 hvalid hfast

theorem sr26p59:∀ i ∈ List.range 1,StrictCheckAt 26 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 59) 26 59:=by decide +kernel
  have hfast:StrictAtFast (row 26 59) 26 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 59) 26 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 59) 26 59 hvalid hfast

theorem sr26p60:∀ i ∈ List.range 1,StrictCheckAt 26 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 60) 26 60:=by decide +kernel
  have hfast:StrictAtFast (row 26 60) 26 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 60) 26 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 60) 26 60 hvalid hfast

theorem sr26p61:∀ i ∈ List.range 1,StrictCheckAt 26 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 61) 26 61:=by decide +kernel
  have hfast:StrictAtFast (row 26 61) 26 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 61) 26 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 61) 26 61 hvalid hfast

theorem sr26p62:∀ i ∈ List.range 1,StrictCheckAt 26 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 62) 26 62:=by decide +kernel
  have hfast:StrictAtFast (row 26 62) 26 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 62) 26 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 62) 26 62 hvalid hfast

theorem sr26p63:∀ i ∈ List.range 1,StrictCheckAt 26 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 63) 26 63:=by decide +kernel
  have hfast:StrictAtFast (row 26 63) 26 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 63) 26 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 63) 26 63 hvalid hfast

theorem sr26p64:∀ i ∈ List.range 1,StrictCheckAt 26 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 64) 26 64:=by decide +kernel
  have hfast:StrictAtFast (row 26 64) 26 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 64) 26 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 64) 26 64 hvalid hfast

theorem sr26p65:∀ i ∈ List.range 1,StrictCheckAt 26 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 65) 26 65:=by decide +kernel
  have hfast:StrictAtFast (row 26 65) 26 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 65) 26 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 65) 26 65 hvalid hfast

theorem sr26p66:∀ i ∈ List.range 1,StrictCheckAt 26 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 66) 26 66:=by decide +kernel
  have hfast:StrictAtFast (row 26 66) 26 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 66) 26 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 66) 26 66 hvalid hfast

theorem sr26p67:∀ i ∈ List.range 1,StrictCheckAt 26 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 67) 26 67:=by decide +kernel
  have hfast:StrictAtFast (row 26 67) 26 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 67) 26 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 67) 26 67 hvalid hfast

theorem sr26p68:∀ i ∈ List.range 1,StrictCheckAt 26 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 68) 26 68:=by decide +kernel
  have hfast:StrictAtFast (row 26 68) 26 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 68) 26 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 68) 26 68 hvalid hfast

theorem sr26p69:∀ i ∈ List.range 1,StrictCheckAt 26 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 69) 26 69:=by decide +kernel
  have hfast:StrictAtFast (row 26 69) 26 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 69) 26 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 69) 26 69 hvalid hfast

theorem sr26p70:∀ i ∈ List.range 1,StrictCheckAt 26 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 70) 26 70:=by decide +kernel
  have hfast:StrictAtFast (row 26 70) 26 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 70) 26 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 70) 26 70 hvalid hfast

theorem sr26p71:∀ i ∈ List.range 1,StrictCheckAt 26 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 71) 26 71:=by decide +kernel
  have hfast:StrictAtFast (row 26 71) 26 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 71) 26 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 71) 26 71 hvalid hfast

theorem sr26p72:∀ i ∈ List.range 1,StrictCheckAt 26 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 72) 26 72:=by decide +kernel
  have hfast:StrictAtFast (row 26 72) 26 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 72) 26 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 72) 26 72 hvalid hfast

theorem sr26p73:∀ i ∈ List.range 1,StrictCheckAt 26 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 73) 26 73:=by decide +kernel
  have hfast:StrictAtFast (row 26 73) 26 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 73) 26 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 73) 26 73 hvalid hfast

theorem sr26p74:∀ i ∈ List.range 1,StrictCheckAt 26 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 74) 26 74:=by decide +kernel
  have hfast:StrictAtFast (row 26 74) 26 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 74) 26 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 74) 26 74 hvalid hfast

theorem sr26p75:∀ i ∈ List.range 1,StrictCheckAt 26 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 75) 26 75:=by decide +kernel
  have hfast:StrictAtFast (row 26 75) 26 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 75) 26 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 75) 26 75 hvalid hfast

theorem sr26p76:∀ i ∈ List.range 1,StrictCheckAt 26 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 76) 26 76:=by decide +kernel
  have hfast:StrictAtFast (row 26 76) 26 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 76) 26 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 76) 26 76 hvalid hfast

theorem sr26p77:∀ i ∈ List.range 1,StrictCheckAt 26 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 77) 26 77:=by decide +kernel
  have hfast:StrictAtFast (row 26 77) 26 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 77) 26 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 77) 26 77 hvalid hfast

theorem sr26p78:∀ i ∈ List.range 1,StrictCheckAt 26 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 78) 26 78:=by decide +kernel
  have hfast:StrictAtFast (row 26 78) 26 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 78) 26 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 78) 26 78 hvalid hfast

theorem sr26p79:∀ i ∈ List.range 1,StrictCheckAt 26 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 79) 26 79:=by decide +kernel
  have hfast:StrictAtFast (row 26 79) 26 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 79) 26 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 79) 26 79 hvalid hfast

theorem sr26p80:∀ i ∈ List.range 1,StrictCheckAt 26 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 80) 26 80:=by decide +kernel
  have hfast:StrictAtFast (row 26 80) 26 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 80) 26 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 80) 26 80 hvalid hfast

theorem sr26p81:∀ i ∈ List.range 1,StrictCheckAt 26 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 81) 26 81:=by decide +kernel
  have hfast:StrictAtFast (row 26 81) 26 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 81) 26 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 81) 26 81 hvalid hfast

theorem sr26p82:∀ i ∈ List.range 1,StrictCheckAt 26 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 82) 26 82:=by decide +kernel
  have hfast:StrictAtFast (row 26 82) 26 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 82) 26 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 82) 26 82 hvalid hfast

theorem sr26p83:∀ i ∈ List.range 1,StrictCheckAt 26 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 83) 26 83:=by decide +kernel
  have hfast:StrictAtFast (row 26 83) 26 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 83) 26 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 83) 26 83 hvalid hfast

theorem sr26p84:∀ i ∈ List.range 1,StrictCheckAt 26 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 84) 26 84:=by decide +kernel
  have hfast:StrictAtFast (row 26 84) 26 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 84) 26 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 84) 26 84 hvalid hfast

theorem sr26p85:∀ i ∈ List.range 1,StrictCheckAt 26 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 85) 26 85:=by decide +kernel
  have hfast:StrictAtFast (row 26 85) 26 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 85) 26 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 85) 26 85 hvalid hfast

theorem sr26p86:∀ i ∈ List.range 1,StrictCheckAt 26 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 86) 26 86:=by decide +kernel
  have hfast:StrictAtFast (row 26 86) 26 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 86) 26 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 86) 26 86 hvalid hfast

theorem sr26p87:∀ i ∈ List.range 1,StrictCheckAt 26 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 87) 26 87:=by decide +kernel
  have hfast:StrictAtFast (row 26 87) 26 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 87) 26 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 87) 26 87 hvalid hfast

theorem sr26p88:∀ i ∈ List.range 1,StrictCheckAt 26 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 88) 26 88:=by decide +kernel
  have hfast:StrictAtFast (row 26 88) 26 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 88) 26 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 88) 26 88 hvalid hfast

theorem sr26p89:∀ i ∈ List.range 1,StrictCheckAt 26 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 89) 26 89:=by decide +kernel
  have hfast:StrictAtFast (row 26 89) 26 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 89) 26 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 89) 26 89 hvalid hfast

theorem sr26p90:∀ i ∈ List.range 1,StrictCheckAt 26 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 90) 26 90:=by decide +kernel
  have hfast:StrictAtFast (row 26 90) 26 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 90) 26 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 90) 26 90 hvalid hfast

theorem sr26p91:∀ i ∈ List.range 1,StrictCheckAt 26 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 91) 26 91:=by decide +kernel
  have hfast:StrictAtFast (row 26 91) 26 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 91) 26 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 91) 26 91 hvalid hfast

theorem sr26p92:∀ i ∈ List.range 1,StrictCheckAt 26 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 92) 26 92:=by decide +kernel
  have hfast:StrictAtFast (row 26 92) 26 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 92) 26 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 92) 26 92 hvalid hfast

theorem sr26p93:∀ i ∈ List.range 1,StrictCheckAt 26 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 93) 26 93:=by decide +kernel
  have hfast:StrictAtFast (row 26 93) 26 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 93) 26 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 93) 26 93 hvalid hfast

theorem sr26p94:∀ i ∈ List.range 1,StrictCheckAt 26 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 94) 26 94:=by decide +kernel
  have hfast:StrictAtFast (row 26 94) 26 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 94) 26 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 94) 26 94 hvalid hfast

theorem sr26p95:∀ i ∈ List.range 1,StrictCheckAt 26 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 95) 26 95:=by decide +kernel
  have hfast:StrictAtFast (row 26 95) 26 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 95) 26 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 95) 26 95 hvalid hfast

theorem sr26p96:∀ i ∈ List.range 1,StrictCheckAt 26 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 96) 26 96:=by decide +kernel
  have hfast:StrictAtFast (row 26 96) 26 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 96) 26 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 96) 26 96 hvalid hfast

theorem sr26p97:∀ i ∈ List.range 1,StrictCheckAt 26 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 97) 26 97:=by decide +kernel
  have hfast:StrictAtFast (row 26 97) 26 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 97) 26 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 97) 26 97 hvalid hfast

theorem sr26p98:∀ i ∈ List.range 1,StrictCheckAt 26 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 98) 26 98:=by decide +kernel
  have hfast:StrictAtFast (row 26 98) 26 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 98) 26 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 98) 26 98 hvalid hfast

theorem sr26p99:∀ i ∈ List.range 1,StrictCheckAt 26 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 99) 26 99:=by decide +kernel
  have hfast:StrictAtFast (row 26 99) 26 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 99) 26 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 99) 26 99 hvalid hfast

theorem sr26p100:∀ i ∈ List.range 1,StrictCheckAt 26 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 100) 26 100:=by decide +kernel
  have hfast:StrictAtFast (row 26 100) 26 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 100) 26 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 100) 26 100 hvalid hfast

theorem sr26p101:∀ i ∈ List.range 1,StrictCheckAt 26 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 101) 26 101:=by decide +kernel
  have hfast:StrictAtFast (row 26 101) 26 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 101) 26 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 101) 26 101 hvalid hfast

theorem sr26p102:∀ i ∈ List.range 1,StrictCheckAt 26 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 102) 26 102:=by decide +kernel
  have hfast:StrictAtFast (row 26 102) 26 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 102) 26 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 102) 26 102 hvalid hfast

theorem sr26p103:∀ i ∈ List.range 1,StrictCheckAt 26 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 103) 26 103:=by decide +kernel
  have hfast:StrictAtFast (row 26 103) 26 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 103) 26 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 103) 26 103 hvalid hfast

theorem sr26p104:∀ i ∈ List.range 1,StrictCheckAt 26 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 104) 26 104:=by decide +kernel
  have hfast:StrictAtFast (row 26 104) 26 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 104) 26 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 104) 26 104 hvalid hfast

theorem sr26p105:∀ i ∈ List.range 1,StrictCheckAt 26 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 105) 26 105:=by decide +kernel
  have hfast:StrictAtFast (row 26 105) 26 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 105) 26 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 105) 26 105 hvalid hfast

theorem sr26p106:∀ i ∈ List.range 1,StrictCheckAt 26 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 106) 26 106:=by decide +kernel
  have hfast:StrictAtFast (row 26 106) 26 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 106) 26 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 106) 26 106 hvalid hfast

theorem sr26p107:∀ i ∈ List.range 1,StrictCheckAt 26 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 107) 26 107:=by decide +kernel
  have hfast:StrictAtFast (row 26 107) 26 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 107) 26 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 107) 26 107 hvalid hfast

theorem sr26p108:∀ i ∈ List.range 1,StrictCheckAt 26 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 108) 26 108:=by decide +kernel
  have hfast:StrictAtFast (row 26 108) 26 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 108) 26 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 108) 26 108 hvalid hfast

theorem sr26p109:∀ i ∈ List.range 1,StrictCheckAt 26 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 109) 26 109:=by decide +kernel
  have hfast:StrictAtFast (row 26 109) 26 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 109) 26 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 109) 26 109 hvalid hfast

theorem sr26p110:∀ i ∈ List.range 1,StrictCheckAt 26 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 110) 26 110:=by decide +kernel
  have hfast:StrictAtFast (row 26 110) 26 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 110) 26 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 110) 26 110 hvalid hfast

theorem sr26p111:∀ i ∈ List.range 1,StrictCheckAt 26 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 111) 26 111:=by decide +kernel
  have hfast:StrictAtFast (row 26 111) 26 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 111) 26 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 111) 26 111 hvalid hfast

theorem sr26p112:∀ i ∈ List.range 1,StrictCheckAt 26 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 112) 26 112:=by decide +kernel
  have hfast:StrictAtFast (row 26 112) 26 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 112) 26 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 112) 26 112 hvalid hfast

theorem sr26p113:∀ i ∈ List.range 1,StrictCheckAt 26 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 113) 26 113:=by decide +kernel
  have hfast:StrictAtFast (row 26 113) 26 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 113) 26 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 113) 26 113 hvalid hfast

theorem sr26p114:∀ i ∈ List.range 1,StrictCheckAt 26 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 114) 26 114:=by decide +kernel
  have hfast:StrictAtFast (row 26 114) 26 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 114) 26 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 114) 26 114 hvalid hfast

theorem sr26p115:∀ i ∈ List.range 1,StrictCheckAt 26 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 115) 26 115:=by decide +kernel
  have hfast:StrictAtFast (row 26 115) 26 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 115) 26 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 115) 26 115 hvalid hfast

theorem sr26p116:∀ i ∈ List.range 1,StrictCheckAt 26 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 26 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 26 116) 26 116:=by decide +kernel
  have hfast:StrictAtFast (row 26 116) 26 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 26 116) 26 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 26 116) 26 116 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
