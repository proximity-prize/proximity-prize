import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr27p0:∀ i ∈ List.range 8,CorrectAt 27 (0+i):=by decide +kernel

theorem cr27p1:∀ i ∈ List.range 8,CorrectAt 27 (8+i):=by decide +kernel

theorem cr27p2:∀ i ∈ List.range 8,CorrectAt 27 (16+i):=by decide +kernel

theorem cr27p3:∀ i ∈ List.range 8,CorrectAt 27 (24+i):=by decide +kernel

theorem cr27p4:∀ i ∈ List.range 8,CorrectAt 27 (32+i):=by decide +kernel

theorem cr27p5:∀ i ∈ List.range 8,CorrectAt 27 (40+i):=by decide +kernel

theorem cr27p6:∀ i ∈ List.range 8,CorrectAt 27 (48+i):=by decide +kernel

theorem cr27p7:∀ i ∈ List.range 8,CorrectAt 27 (56+i):=by decide +kernel

theorem cr27p8:∀ i ∈ List.range 8,CorrectAt 27 (64+i):=by decide +kernel

theorem cr27p9:∀ i ∈ List.range 8,CorrectAt 27 (72+i):=by decide +kernel

theorem cr27p10:∀ i ∈ List.range 8,CorrectAt 27 (80+i):=by decide +kernel

theorem cr27p11:∀ i ∈ List.range 8,CorrectAt 27 (88+i):=by decide +kernel

theorem cr27p12:∀ i ∈ List.range 8,CorrectAt 27 (96+i):=by decide +kernel

theorem cr27p13:∀ i ∈ List.range 8,CorrectAt 27 (104+i):=by decide +kernel

theorem cr27p14:∀ i ∈ List.range 4,CorrectAt 27 (112+i):=by decide +kernel

theorem sr27p0:∀ i ∈ List.range 1,StrictCheckAt 27 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 0) 27 0:=by decide +kernel
  have hfast:StrictAtFast (row 27 0) 27 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 0) 27 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 0) 27 0 hvalid hfast

theorem sr27p1:∀ i ∈ List.range 1,StrictCheckAt 27 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 1) 27 1:=by decide +kernel
  have hfast:StrictAtFast (row 27 1) 27 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 1) 27 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 1) 27 1 hvalid hfast

theorem sr27p2:∀ i ∈ List.range 1,StrictCheckAt 27 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 2) 27 2:=by decide +kernel
  have hfast:StrictAtFast (row 27 2) 27 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 2) 27 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 2) 27 2 hvalid hfast

theorem sr27p3:∀ i ∈ List.range 1,StrictCheckAt 27 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 3) 27 3:=by decide +kernel
  have hfast:StrictAtFast (row 27 3) 27 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 3) 27 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 3) 27 3 hvalid hfast

theorem sr27p4:∀ i ∈ List.range 1,StrictCheckAt 27 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 4) 27 4:=by decide +kernel
  have hfast:StrictAtFast (row 27 4) 27 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 4) 27 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 4) 27 4 hvalid hfast

theorem sr27p5:∀ i ∈ List.range 1,StrictCheckAt 27 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 5) 27 5:=by decide +kernel
  have hfast:StrictAtFast (row 27 5) 27 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 5) 27 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 5) 27 5 hvalid hfast

theorem sr27p6:∀ i ∈ List.range 1,StrictCheckAt 27 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 6) 27 6:=by decide +kernel
  have hfast:StrictAtFast (row 27 6) 27 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 6) 27 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 6) 27 6 hvalid hfast

theorem sr27p7:∀ i ∈ List.range 1,StrictCheckAt 27 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 7) 27 7:=by decide +kernel
  have hfast:StrictAtFast (row 27 7) 27 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 7) 27 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 7) 27 7 hvalid hfast

theorem sr27p8:∀ i ∈ List.range 1,StrictCheckAt 27 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 8) 27 8:=by decide +kernel
  have hfast:StrictAtFast (row 27 8) 27 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 8) 27 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 8) 27 8 hvalid hfast

theorem sr27p9:∀ i ∈ List.range 1,StrictCheckAt 27 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 9) 27 9:=by decide +kernel
  have hfast:StrictAtFast (row 27 9) 27 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 9) 27 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 9) 27 9 hvalid hfast

theorem sr27p10:∀ i ∈ List.range 1,StrictCheckAt 27 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 10) 27 10:=by decide +kernel
  have hfast:StrictAtFast (row 27 10) 27 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 10) 27 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 10) 27 10 hvalid hfast

theorem sr27p11:∀ i ∈ List.range 1,StrictCheckAt 27 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 11) 27 11:=by decide +kernel
  have hfast:StrictAtFast (row 27 11) 27 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 11) 27 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 11) 27 11 hvalid hfast

theorem sr27p12:∀ i ∈ List.range 1,StrictCheckAt 27 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 12) 27 12:=by decide +kernel
  have hfast:StrictAtFast (row 27 12) 27 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 12) 27 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 12) 27 12 hvalid hfast

theorem sr27p13:∀ i ∈ List.range 1,StrictCheckAt 27 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 13) 27 13:=by decide +kernel
  have hfast:StrictAtFast (row 27 13) 27 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 13) 27 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 13) 27 13 hvalid hfast

theorem sr27p14:∀ i ∈ List.range 1,StrictCheckAt 27 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 14) 27 14:=by decide +kernel
  have hfast:StrictAtFast (row 27 14) 27 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 14) 27 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 14) 27 14 hvalid hfast

theorem sr27p15:∀ i ∈ List.range 1,StrictCheckAt 27 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 15) 27 15:=by decide +kernel
  have hfast:StrictAtFast (row 27 15) 27 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 15) 27 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 15) 27 15 hvalid hfast

theorem sr27p16:∀ i ∈ List.range 1,StrictCheckAt 27 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 16) 27 16:=by decide +kernel
  have hfast:StrictAtFast (row 27 16) 27 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 16) 27 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 16) 27 16 hvalid hfast

theorem sr27p17:∀ i ∈ List.range 1,StrictCheckAt 27 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 17) 27 17:=by decide +kernel
  have hfast:StrictAtFast (row 27 17) 27 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 17) 27 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 17) 27 17 hvalid hfast

theorem sr27p18:∀ i ∈ List.range 1,StrictCheckAt 27 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 18) 27 18:=by decide +kernel
  have hfast:StrictAtFast (row 27 18) 27 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 18) 27 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 18) 27 18 hvalid hfast

theorem sr27p19:∀ i ∈ List.range 1,StrictCheckAt 27 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 19) 27 19:=by decide +kernel
  have hfast:StrictAtFast (row 27 19) 27 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 19) 27 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 19) 27 19 hvalid hfast

theorem sr27p20:∀ i ∈ List.range 1,StrictCheckAt 27 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 20) 27 20:=by decide +kernel
  have hfast:StrictAtFast (row 27 20) 27 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 20) 27 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 20) 27 20 hvalid hfast

theorem sr27p21:∀ i ∈ List.range 1,StrictCheckAt 27 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 21) 27 21:=by decide +kernel
  have hfast:StrictAtFast (row 27 21) 27 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 21) 27 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 21) 27 21 hvalid hfast

theorem sr27p22:∀ i ∈ List.range 1,StrictCheckAt 27 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 22) 27 22:=by decide +kernel
  have hfast:StrictAtFast (row 27 22) 27 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 22) 27 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 22) 27 22 hvalid hfast

theorem sr27p23:∀ i ∈ List.range 1,StrictCheckAt 27 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 23) 27 23:=by decide +kernel
  have hfast:StrictAtFast (row 27 23) 27 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 23) 27 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 23) 27 23 hvalid hfast

theorem sr27p24:∀ i ∈ List.range 1,StrictCheckAt 27 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 24) 27 24:=by decide +kernel
  have hfast:StrictAtFast (row 27 24) 27 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 24) 27 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 24) 27 24 hvalid hfast

theorem sr27p25:∀ i ∈ List.range 1,StrictCheckAt 27 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 25) 27 25:=by decide +kernel
  have hfast:StrictAtFast (row 27 25) 27 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 25) 27 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 25) 27 25 hvalid hfast

theorem sr27p26:∀ i ∈ List.range 1,StrictCheckAt 27 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 26) 27 26:=by decide +kernel
  have hfast:StrictAtFast (row 27 26) 27 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 26) 27 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 26) 27 26 hvalid hfast

theorem sr27p27:∀ i ∈ List.range 1,StrictCheckAt 27 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 27) 27 27:=by decide +kernel
  have hfast:StrictAtFast (row 27 27) 27 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 27) 27 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 27) 27 27 hvalid hfast

theorem sr27p28:∀ i ∈ List.range 1,StrictCheckAt 27 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 28) 27 28:=by decide +kernel
  have hfast:StrictAtFast (row 27 28) 27 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 28) 27 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 28) 27 28 hvalid hfast

theorem sr27p29:∀ i ∈ List.range 1,StrictCheckAt 27 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 29) 27 29:=by decide +kernel
  have hfast:StrictAtFast (row 27 29) 27 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 29) 27 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 29) 27 29 hvalid hfast

theorem sr27p30:∀ i ∈ List.range 1,StrictCheckAt 27 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 30) 27 30:=by decide +kernel
  have hfast:StrictAtFast (row 27 30) 27 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 30) 27 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 30) 27 30 hvalid hfast

theorem sr27p31:∀ i ∈ List.range 1,StrictCheckAt 27 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 31) 27 31:=by decide +kernel
  have hfast:StrictAtFast (row 27 31) 27 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 31) 27 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 31) 27 31 hvalid hfast

theorem sr27p32:∀ i ∈ List.range 1,StrictCheckAt 27 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 32) 27 32:=by decide +kernel
  have hfast:StrictAtFast (row 27 32) 27 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 32) 27 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 32) 27 32 hvalid hfast

theorem sr27p33:∀ i ∈ List.range 1,StrictCheckAt 27 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 33) 27 33:=by decide +kernel
  have hfast:StrictAtFast (row 27 33) 27 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 33) 27 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 33) 27 33 hvalid hfast

theorem sr27p34:∀ i ∈ List.range 1,StrictCheckAt 27 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 34) 27 34:=by decide +kernel
  have hfast:StrictAtFast (row 27 34) 27 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 34) 27 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 34) 27 34 hvalid hfast

theorem sr27p35:∀ i ∈ List.range 1,StrictCheckAt 27 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 35) 27 35:=by decide +kernel
  have hfast:StrictAtFast (row 27 35) 27 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 35) 27 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 35) 27 35 hvalid hfast

theorem sr27p36:∀ i ∈ List.range 1,StrictCheckAt 27 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 36) 27 36:=by decide +kernel
  have hfast:StrictAtFast (row 27 36) 27 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 36) 27 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 36) 27 36 hvalid hfast

theorem sr27p37:∀ i ∈ List.range 1,StrictCheckAt 27 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 37) 27 37:=by decide +kernel
  have hfast:StrictAtFast (row 27 37) 27 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 37) 27 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 37) 27 37 hvalid hfast

theorem sr27p38:∀ i ∈ List.range 1,StrictCheckAt 27 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 38) 27 38:=by decide +kernel
  have hfast:StrictAtFast (row 27 38) 27 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 38) 27 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 38) 27 38 hvalid hfast

theorem sr27p39:∀ i ∈ List.range 1,StrictCheckAt 27 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 39) 27 39:=by decide +kernel
  have hfast:StrictAtFast (row 27 39) 27 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 39) 27 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 39) 27 39 hvalid hfast

theorem sr27p40:∀ i ∈ List.range 1,StrictCheckAt 27 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 40) 27 40:=by decide +kernel
  have hfast:StrictAtFast (row 27 40) 27 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 40) 27 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 40) 27 40 hvalid hfast

theorem sr27p41:∀ i ∈ List.range 1,StrictCheckAt 27 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 41) 27 41:=by decide +kernel
  have hfast:StrictAtFast (row 27 41) 27 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 41) 27 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 41) 27 41 hvalid hfast

theorem sr27p42:∀ i ∈ List.range 1,StrictCheckAt 27 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 42) 27 42:=by decide +kernel
  have hfast:StrictAtFast (row 27 42) 27 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 42) 27 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 42) 27 42 hvalid hfast

theorem sr27p43:∀ i ∈ List.range 1,StrictCheckAt 27 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 43) 27 43:=by decide +kernel
  have hfast:StrictAtFast (row 27 43) 27 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 43) 27 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 43) 27 43 hvalid hfast

theorem sr27p44:∀ i ∈ List.range 1,StrictCheckAt 27 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 44) 27 44:=by decide +kernel
  have hfast:StrictAtFast (row 27 44) 27 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 44) 27 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 44) 27 44 hvalid hfast

theorem sr27p45:∀ i ∈ List.range 1,StrictCheckAt 27 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 45) 27 45:=by decide +kernel
  have hfast:StrictAtFast (row 27 45) 27 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 45) 27 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 45) 27 45 hvalid hfast

theorem sr27p46:∀ i ∈ List.range 1,StrictCheckAt 27 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 46) 27 46:=by decide +kernel
  have hfast:StrictAtFast (row 27 46) 27 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 46) 27 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 46) 27 46 hvalid hfast

theorem sr27p47:∀ i ∈ List.range 1,StrictCheckAt 27 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 47) 27 47:=by decide +kernel
  have hfast:StrictAtFast (row 27 47) 27 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 47) 27 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 47) 27 47 hvalid hfast

theorem sr27p48:∀ i ∈ List.range 1,StrictCheckAt 27 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 48) 27 48:=by decide +kernel
  have hfast:StrictAtFast (row 27 48) 27 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 48) 27 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 48) 27 48 hvalid hfast

theorem sr27p49:∀ i ∈ List.range 1,StrictCheckAt 27 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 49) 27 49:=by decide +kernel
  have hfast:StrictAtFast (row 27 49) 27 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 49) 27 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 49) 27 49 hvalid hfast

theorem sr27p50:∀ i ∈ List.range 1,StrictCheckAt 27 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 50) 27 50:=by decide +kernel
  have hfast:StrictAtFast (row 27 50) 27 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 50) 27 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 50) 27 50 hvalid hfast

theorem sr27p51:∀ i ∈ List.range 1,StrictCheckAt 27 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 51) 27 51:=by decide +kernel
  have hfast:StrictAtFast (row 27 51) 27 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 51) 27 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 51) 27 51 hvalid hfast

theorem sr27p52:∀ i ∈ List.range 1,StrictCheckAt 27 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 52) 27 52:=by decide +kernel
  have hfast:StrictAtFast (row 27 52) 27 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 52) 27 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 52) 27 52 hvalid hfast

theorem sr27p53:∀ i ∈ List.range 1,StrictCheckAt 27 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 53) 27 53:=by decide +kernel
  have hfast:StrictAtFast (row 27 53) 27 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 53) 27 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 53) 27 53 hvalid hfast

theorem sr27p54:∀ i ∈ List.range 1,StrictCheckAt 27 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 54) 27 54:=by decide +kernel
  have hfast:StrictAtFast (row 27 54) 27 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 54) 27 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 54) 27 54 hvalid hfast

theorem sr27p55:∀ i ∈ List.range 1,StrictCheckAt 27 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 55) 27 55:=by decide +kernel
  have hfast:StrictAtFast (row 27 55) 27 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 55) 27 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 55) 27 55 hvalid hfast

theorem sr27p56:∀ i ∈ List.range 1,StrictCheckAt 27 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 56) 27 56:=by decide +kernel
  have hfast:StrictAtFast (row 27 56) 27 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 56) 27 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 56) 27 56 hvalid hfast

theorem sr27p57:∀ i ∈ List.range 1,StrictCheckAt 27 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 57) 27 57:=by decide +kernel
  have hfast:StrictAtFast (row 27 57) 27 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 57) 27 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 57) 27 57 hvalid hfast

theorem sr27p58:∀ i ∈ List.range 1,StrictCheckAt 27 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 58) 27 58:=by decide +kernel
  have hfast:StrictAtFast (row 27 58) 27 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 58) 27 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 58) 27 58 hvalid hfast

theorem sr27p59:∀ i ∈ List.range 1,StrictCheckAt 27 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 59) 27 59:=by decide +kernel
  have hfast:StrictAtFast (row 27 59) 27 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 59) 27 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 59) 27 59 hvalid hfast

theorem sr27p60:∀ i ∈ List.range 1,StrictCheckAt 27 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 60) 27 60:=by decide +kernel
  have hfast:StrictAtFast (row 27 60) 27 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 60) 27 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 60) 27 60 hvalid hfast

theorem sr27p61:∀ i ∈ List.range 1,StrictCheckAt 27 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 61) 27 61:=by decide +kernel
  have hfast:StrictAtFast (row 27 61) 27 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 61) 27 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 61) 27 61 hvalid hfast

theorem sr27p62:∀ i ∈ List.range 1,StrictCheckAt 27 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 62) 27 62:=by decide +kernel
  have hfast:StrictAtFast (row 27 62) 27 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 62) 27 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 62) 27 62 hvalid hfast

theorem sr27p63:∀ i ∈ List.range 1,StrictCheckAt 27 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 63) 27 63:=by decide +kernel
  have hfast:StrictAtFast (row 27 63) 27 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 63) 27 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 63) 27 63 hvalid hfast

theorem sr27p64:∀ i ∈ List.range 1,StrictCheckAt 27 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 64) 27 64:=by decide +kernel
  have hfast:StrictAtFast (row 27 64) 27 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 64) 27 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 64) 27 64 hvalid hfast

theorem sr27p65:∀ i ∈ List.range 1,StrictCheckAt 27 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 65) 27 65:=by decide +kernel
  have hfast:StrictAtFast (row 27 65) 27 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 65) 27 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 65) 27 65 hvalid hfast

theorem sr27p66:∀ i ∈ List.range 1,StrictCheckAt 27 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 66) 27 66:=by decide +kernel
  have hfast:StrictAtFast (row 27 66) 27 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 66) 27 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 66) 27 66 hvalid hfast

theorem sr27p67:∀ i ∈ List.range 1,StrictCheckAt 27 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 67) 27 67:=by decide +kernel
  have hfast:StrictAtFast (row 27 67) 27 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 67) 27 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 67) 27 67 hvalid hfast

theorem sr27p68:∀ i ∈ List.range 1,StrictCheckAt 27 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 68) 27 68:=by decide +kernel
  have hfast:StrictAtFast (row 27 68) 27 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 68) 27 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 68) 27 68 hvalid hfast

theorem sr27p69:∀ i ∈ List.range 1,StrictCheckAt 27 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 69) 27 69:=by decide +kernel
  have hfast:StrictAtFast (row 27 69) 27 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 69) 27 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 69) 27 69 hvalid hfast

theorem sr27p70:∀ i ∈ List.range 1,StrictCheckAt 27 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 70) 27 70:=by decide +kernel
  have hfast:StrictAtFast (row 27 70) 27 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 70) 27 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 70) 27 70 hvalid hfast

theorem sr27p71:∀ i ∈ List.range 1,StrictCheckAt 27 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 71) 27 71:=by decide +kernel
  have hfast:StrictAtFast (row 27 71) 27 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 71) 27 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 71) 27 71 hvalid hfast

theorem sr27p72:∀ i ∈ List.range 1,StrictCheckAt 27 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 72) 27 72:=by decide +kernel
  have hfast:StrictAtFast (row 27 72) 27 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 72) 27 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 72) 27 72 hvalid hfast

theorem sr27p73:∀ i ∈ List.range 1,StrictCheckAt 27 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 73) 27 73:=by decide +kernel
  have hfast:StrictAtFast (row 27 73) 27 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 73) 27 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 73) 27 73 hvalid hfast

theorem sr27p74:∀ i ∈ List.range 1,StrictCheckAt 27 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 74) 27 74:=by decide +kernel
  have hfast:StrictAtFast (row 27 74) 27 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 74) 27 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 74) 27 74 hvalid hfast

theorem sr27p75:∀ i ∈ List.range 1,StrictCheckAt 27 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 75) 27 75:=by decide +kernel
  have hfast:StrictAtFast (row 27 75) 27 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 75) 27 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 75) 27 75 hvalid hfast

theorem sr27p76:∀ i ∈ List.range 1,StrictCheckAt 27 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 76) 27 76:=by decide +kernel
  have hfast:StrictAtFast (row 27 76) 27 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 76) 27 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 76) 27 76 hvalid hfast

theorem sr27p77:∀ i ∈ List.range 1,StrictCheckAt 27 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 77) 27 77:=by decide +kernel
  have hfast:StrictAtFast (row 27 77) 27 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 77) 27 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 77) 27 77 hvalid hfast

theorem sr27p78:∀ i ∈ List.range 1,StrictCheckAt 27 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 78) 27 78:=by decide +kernel
  have hfast:StrictAtFast (row 27 78) 27 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 78) 27 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 78) 27 78 hvalid hfast

theorem sr27p79:∀ i ∈ List.range 1,StrictCheckAt 27 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 79) 27 79:=by decide +kernel
  have hfast:StrictAtFast (row 27 79) 27 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 79) 27 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 79) 27 79 hvalid hfast

theorem sr27p80:∀ i ∈ List.range 1,StrictCheckAt 27 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 80) 27 80:=by decide +kernel
  have hfast:StrictAtFast (row 27 80) 27 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 80) 27 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 80) 27 80 hvalid hfast

theorem sr27p81:∀ i ∈ List.range 1,StrictCheckAt 27 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 81) 27 81:=by decide +kernel
  have hfast:StrictAtFast (row 27 81) 27 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 81) 27 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 81) 27 81 hvalid hfast

theorem sr27p82:∀ i ∈ List.range 1,StrictCheckAt 27 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 82) 27 82:=by decide +kernel
  have hfast:StrictAtFast (row 27 82) 27 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 82) 27 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 82) 27 82 hvalid hfast

theorem sr27p83:∀ i ∈ List.range 1,StrictCheckAt 27 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 83) 27 83:=by decide +kernel
  have hfast:StrictAtFast (row 27 83) 27 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 83) 27 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 83) 27 83 hvalid hfast

theorem sr27p84:∀ i ∈ List.range 1,StrictCheckAt 27 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 84) 27 84:=by decide +kernel
  have hfast:StrictAtFast (row 27 84) 27 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 84) 27 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 84) 27 84 hvalid hfast

theorem sr27p85:∀ i ∈ List.range 1,StrictCheckAt 27 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 85) 27 85:=by decide +kernel
  have hfast:StrictAtFast (row 27 85) 27 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 85) 27 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 85) 27 85 hvalid hfast

theorem sr27p86:∀ i ∈ List.range 1,StrictCheckAt 27 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 86) 27 86:=by decide +kernel
  have hfast:StrictAtFast (row 27 86) 27 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 86) 27 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 86) 27 86 hvalid hfast

theorem sr27p87:∀ i ∈ List.range 1,StrictCheckAt 27 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 87) 27 87:=by decide +kernel
  have hfast:StrictAtFast (row 27 87) 27 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 87) 27 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 87) 27 87 hvalid hfast

theorem sr27p88:∀ i ∈ List.range 1,StrictCheckAt 27 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 88) 27 88:=by decide +kernel
  have hfast:StrictAtFast (row 27 88) 27 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 88) 27 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 88) 27 88 hvalid hfast

theorem sr27p89:∀ i ∈ List.range 1,StrictCheckAt 27 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 89) 27 89:=by decide +kernel
  have hfast:StrictAtFast (row 27 89) 27 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 89) 27 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 89) 27 89 hvalid hfast

theorem sr27p90:∀ i ∈ List.range 1,StrictCheckAt 27 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 90) 27 90:=by decide +kernel
  have hfast:StrictAtFast (row 27 90) 27 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 90) 27 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 90) 27 90 hvalid hfast

theorem sr27p91:∀ i ∈ List.range 1,StrictCheckAt 27 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 91) 27 91:=by decide +kernel
  have hfast:StrictAtFast (row 27 91) 27 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 91) 27 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 91) 27 91 hvalid hfast

theorem sr27p92:∀ i ∈ List.range 1,StrictCheckAt 27 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 92) 27 92:=by decide +kernel
  have hfast:StrictAtFast (row 27 92) 27 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 92) 27 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 92) 27 92 hvalid hfast

theorem sr27p93:∀ i ∈ List.range 1,StrictCheckAt 27 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 93) 27 93:=by decide +kernel
  have hfast:StrictAtFast (row 27 93) 27 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 93) 27 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 93) 27 93 hvalid hfast

theorem sr27p94:∀ i ∈ List.range 1,StrictCheckAt 27 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 94) 27 94:=by decide +kernel
  have hfast:StrictAtFast (row 27 94) 27 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 94) 27 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 94) 27 94 hvalid hfast

theorem sr27p95:∀ i ∈ List.range 1,StrictCheckAt 27 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 95) 27 95:=by decide +kernel
  have hfast:StrictAtFast (row 27 95) 27 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 95) 27 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 95) 27 95 hvalid hfast

theorem sr27p96:∀ i ∈ List.range 1,StrictCheckAt 27 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 96) 27 96:=by decide +kernel
  have hfast:StrictAtFast (row 27 96) 27 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 96) 27 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 96) 27 96 hvalid hfast

theorem sr27p97:∀ i ∈ List.range 1,StrictCheckAt 27 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 97) 27 97:=by decide +kernel
  have hfast:StrictAtFast (row 27 97) 27 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 97) 27 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 97) 27 97 hvalid hfast

theorem sr27p98:∀ i ∈ List.range 1,StrictCheckAt 27 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 98) 27 98:=by decide +kernel
  have hfast:StrictAtFast (row 27 98) 27 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 98) 27 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 98) 27 98 hvalid hfast

theorem sr27p99:∀ i ∈ List.range 1,StrictCheckAt 27 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 99) 27 99:=by decide +kernel
  have hfast:StrictAtFast (row 27 99) 27 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 99) 27 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 99) 27 99 hvalid hfast

theorem sr27p100:∀ i ∈ List.range 1,StrictCheckAt 27 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 100) 27 100:=by decide +kernel
  have hfast:StrictAtFast (row 27 100) 27 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 100) 27 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 100) 27 100 hvalid hfast

theorem sr27p101:∀ i ∈ List.range 1,StrictCheckAt 27 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 101) 27 101:=by decide +kernel
  have hfast:StrictAtFast (row 27 101) 27 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 101) 27 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 101) 27 101 hvalid hfast

theorem sr27p102:∀ i ∈ List.range 1,StrictCheckAt 27 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 102) 27 102:=by decide +kernel
  have hfast:StrictAtFast (row 27 102) 27 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 102) 27 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 102) 27 102 hvalid hfast

theorem sr27p103:∀ i ∈ List.range 1,StrictCheckAt 27 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 103) 27 103:=by decide +kernel
  have hfast:StrictAtFast (row 27 103) 27 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 103) 27 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 103) 27 103 hvalid hfast

theorem sr27p104:∀ i ∈ List.range 1,StrictCheckAt 27 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 104) 27 104:=by decide +kernel
  have hfast:StrictAtFast (row 27 104) 27 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 104) 27 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 104) 27 104 hvalid hfast

theorem sr27p105:∀ i ∈ List.range 1,StrictCheckAt 27 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 105) 27 105:=by decide +kernel
  have hfast:StrictAtFast (row 27 105) 27 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 105) 27 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 105) 27 105 hvalid hfast

theorem sr27p106:∀ i ∈ List.range 1,StrictCheckAt 27 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 106) 27 106:=by decide +kernel
  have hfast:StrictAtFast (row 27 106) 27 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 106) 27 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 106) 27 106 hvalid hfast

theorem sr27p107:∀ i ∈ List.range 1,StrictCheckAt 27 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 107) 27 107:=by decide +kernel
  have hfast:StrictAtFast (row 27 107) 27 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 107) 27 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 107) 27 107 hvalid hfast

theorem sr27p108:∀ i ∈ List.range 1,StrictCheckAt 27 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 108) 27 108:=by decide +kernel
  have hfast:StrictAtFast (row 27 108) 27 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 108) 27 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 108) 27 108 hvalid hfast

theorem sr27p109:∀ i ∈ List.range 1,StrictCheckAt 27 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 109) 27 109:=by decide +kernel
  have hfast:StrictAtFast (row 27 109) 27 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 109) 27 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 109) 27 109 hvalid hfast

theorem sr27p110:∀ i ∈ List.range 1,StrictCheckAt 27 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 110) 27 110:=by decide +kernel
  have hfast:StrictAtFast (row 27 110) 27 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 110) 27 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 110) 27 110 hvalid hfast

theorem sr27p111:∀ i ∈ List.range 1,StrictCheckAt 27 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 111) 27 111:=by decide +kernel
  have hfast:StrictAtFast (row 27 111) 27 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 111) 27 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 111) 27 111 hvalid hfast

theorem sr27p112:∀ i ∈ List.range 1,StrictCheckAt 27 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 112) 27 112:=by decide +kernel
  have hfast:StrictAtFast (row 27 112) 27 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 112) 27 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 112) 27 112 hvalid hfast

theorem sr27p113:∀ i ∈ List.range 1,StrictCheckAt 27 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 113) 27 113:=by decide +kernel
  have hfast:StrictAtFast (row 27 113) 27 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 113) 27 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 113) 27 113 hvalid hfast

theorem sr27p114:∀ i ∈ List.range 1,StrictCheckAt 27 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 114) 27 114:=by decide +kernel
  have hfast:StrictAtFast (row 27 114) 27 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 114) 27 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 114) 27 114 hvalid hfast

theorem sr27p115:∀ i ∈ List.range 1,StrictCheckAt 27 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 115) 27 115:=by decide +kernel
  have hfast:StrictAtFast (row 27 115) 27 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 115) 27 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 115) 27 115 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
