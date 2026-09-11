import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr16p0:∀ i ∈ List.range 8,CorrectAt 16 (0+i):=by decide +kernel

theorem cr16p1:∀ i ∈ List.range 8,CorrectAt 16 (8+i):=by decide +kernel

theorem cr16p2:∀ i ∈ List.range 8,CorrectAt 16 (16+i):=by decide +kernel

theorem cr16p3:∀ i ∈ List.range 8,CorrectAt 16 (24+i):=by decide +kernel

theorem cr16p4:∀ i ∈ List.range 8,CorrectAt 16 (32+i):=by decide +kernel

theorem cr16p5:∀ i ∈ List.range 8,CorrectAt 16 (40+i):=by decide +kernel

theorem cr16p6:∀ i ∈ List.range 8,CorrectAt 16 (48+i):=by decide +kernel

theorem cr16p7:∀ i ∈ List.range 8,CorrectAt 16 (56+i):=by decide +kernel

theorem cr16p8:∀ i ∈ List.range 8,CorrectAt 16 (64+i):=by decide +kernel

theorem cr16p9:∀ i ∈ List.range 8,CorrectAt 16 (72+i):=by decide +kernel

theorem cr16p10:∀ i ∈ List.range 8,CorrectAt 16 (80+i):=by decide +kernel

theorem cr16p11:∀ i ∈ List.range 8,CorrectAt 16 (88+i):=by decide +kernel

theorem cr16p12:∀ i ∈ List.range 8,CorrectAt 16 (96+i):=by decide +kernel

theorem cr16p13:∀ i ∈ List.range 8,CorrectAt 16 (104+i):=by decide +kernel

theorem cr16p14:∀ i ∈ List.range 8,CorrectAt 16 (112+i):=by decide +kernel

theorem cr16p15:∀ i ∈ List.range 7,CorrectAt 16 (120+i):=by decide +kernel

theorem sr16p0:∀ i ∈ List.range 1,StrictCheckAt 16 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 0) 16 0:=by decide +kernel
  have hfast:StrictAtFast (row 16 0) 16 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 0) 16 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 0) 16 0 hvalid hfast

theorem sr16p1:∀ i ∈ List.range 1,StrictCheckAt 16 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 1) 16 1:=by decide +kernel
  have hfast:StrictAtFast (row 16 1) 16 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 1) 16 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 1) 16 1 hvalid hfast

theorem sr16p2:∀ i ∈ List.range 1,StrictCheckAt 16 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 2) 16 2:=by decide +kernel
  have hfast:StrictAtFast (row 16 2) 16 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 2) 16 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 2) 16 2 hvalid hfast

theorem sr16p3:∀ i ∈ List.range 1,StrictCheckAt 16 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 3) 16 3:=by decide +kernel
  have hfast:StrictAtFast (row 16 3) 16 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 3) 16 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 3) 16 3 hvalid hfast

theorem sr16p4:∀ i ∈ List.range 1,StrictCheckAt 16 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 4) 16 4:=by decide +kernel
  have hfast:StrictAtFast (row 16 4) 16 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 4) 16 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 4) 16 4 hvalid hfast

theorem sr16p5:∀ i ∈ List.range 1,StrictCheckAt 16 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 5) 16 5:=by decide +kernel
  have hfast:StrictAtFast (row 16 5) 16 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 5) 16 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 5) 16 5 hvalid hfast

theorem sr16p6:∀ i ∈ List.range 1,StrictCheckAt 16 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 6) 16 6:=by decide +kernel
  have hfast:StrictAtFast (row 16 6) 16 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 6) 16 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 6) 16 6 hvalid hfast

theorem sr16p7:∀ i ∈ List.range 1,StrictCheckAt 16 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 7) 16 7:=by decide +kernel
  have hfast:StrictAtFast (row 16 7) 16 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 7) 16 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 7) 16 7 hvalid hfast

theorem sr16p8:∀ i ∈ List.range 1,StrictCheckAt 16 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 8) 16 8:=by decide +kernel
  have hfast:StrictAtFast (row 16 8) 16 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 8) 16 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 8) 16 8 hvalid hfast

theorem sr16p9:∀ i ∈ List.range 1,StrictCheckAt 16 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 9) 16 9:=by decide +kernel
  have hfast:StrictAtFast (row 16 9) 16 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 9) 16 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 9) 16 9 hvalid hfast

theorem sr16p10:∀ i ∈ List.range 1,StrictCheckAt 16 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 10) 16 10:=by decide +kernel
  have hfast:StrictAtFast (row 16 10) 16 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 10) 16 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 10) 16 10 hvalid hfast

theorem sr16p11:∀ i ∈ List.range 1,StrictCheckAt 16 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 11) 16 11:=by decide +kernel
  have hfast:StrictAtFast (row 16 11) 16 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 11) 16 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 11) 16 11 hvalid hfast

theorem sr16p12:∀ i ∈ List.range 1,StrictCheckAt 16 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 12) 16 12:=by decide +kernel
  have hfast:StrictAtFast (row 16 12) 16 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 12) 16 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 12) 16 12 hvalid hfast

theorem sr16p13:∀ i ∈ List.range 1,StrictCheckAt 16 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 13) 16 13:=by decide +kernel
  have hfast:StrictAtFast (row 16 13) 16 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 13) 16 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 13) 16 13 hvalid hfast

theorem sr16p14:∀ i ∈ List.range 1,StrictCheckAt 16 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 14) 16 14:=by decide +kernel
  have hfast:StrictAtFast (row 16 14) 16 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 14) 16 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 14) 16 14 hvalid hfast

theorem sr16p15:∀ i ∈ List.range 1,StrictCheckAt 16 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 15) 16 15:=by decide +kernel
  have hfast:StrictAtFast (row 16 15) 16 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 15) 16 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 15) 16 15 hvalid hfast

theorem sr16p16:∀ i ∈ List.range 1,StrictCheckAt 16 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 16) 16 16:=by decide +kernel
  have hfast:StrictAtFast (row 16 16) 16 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 16) 16 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 16) 16 16 hvalid hfast

theorem sr16p17:∀ i ∈ List.range 1,StrictCheckAt 16 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 17) 16 17:=by decide +kernel
  have hfast:StrictAtFast (row 16 17) 16 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 17) 16 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 17) 16 17 hvalid hfast

theorem sr16p18:∀ i ∈ List.range 1,StrictCheckAt 16 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 18) 16 18:=by decide +kernel
  have hfast:StrictAtFast (row 16 18) 16 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 18) 16 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 18) 16 18 hvalid hfast

theorem sr16p19:∀ i ∈ List.range 1,StrictCheckAt 16 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 19) 16 19:=by decide +kernel
  have hfast:StrictAtFast (row 16 19) 16 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 19) 16 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 19) 16 19 hvalid hfast

theorem sr16p20:∀ i ∈ List.range 1,StrictCheckAt 16 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 20) 16 20:=by decide +kernel
  have hfast:StrictAtFast (row 16 20) 16 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 20) 16 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 20) 16 20 hvalid hfast

theorem sr16p21:∀ i ∈ List.range 1,StrictCheckAt 16 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 21) 16 21:=by decide +kernel
  have hfast:StrictAtFast (row 16 21) 16 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 21) 16 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 21) 16 21 hvalid hfast

theorem sr16p22:∀ i ∈ List.range 1,StrictCheckAt 16 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 22) 16 22:=by decide +kernel
  have hfast:StrictAtFast (row 16 22) 16 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 22) 16 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 22) 16 22 hvalid hfast

theorem sr16p23:∀ i ∈ List.range 1,StrictCheckAt 16 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 23) 16 23:=by decide +kernel
  have hfast:StrictAtFast (row 16 23) 16 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 23) 16 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 23) 16 23 hvalid hfast

theorem sr16p24:∀ i ∈ List.range 1,StrictCheckAt 16 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 24) 16 24:=by decide +kernel
  have hfast:StrictAtFast (row 16 24) 16 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 24) 16 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 24) 16 24 hvalid hfast

theorem sr16p25:∀ i ∈ List.range 1,StrictCheckAt 16 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 25) 16 25:=by decide +kernel
  have hfast:StrictAtFast (row 16 25) 16 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 25) 16 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 25) 16 25 hvalid hfast

theorem sr16p26:∀ i ∈ List.range 1,StrictCheckAt 16 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 26) 16 26:=by decide +kernel
  have hfast:StrictAtFast (row 16 26) 16 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 26) 16 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 26) 16 26 hvalid hfast

theorem sr16p27:∀ i ∈ List.range 1,StrictCheckAt 16 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 27) 16 27:=by decide +kernel
  have hfast:StrictAtFast (row 16 27) 16 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 27) 16 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 27) 16 27 hvalid hfast

theorem sr16p28:∀ i ∈ List.range 1,StrictCheckAt 16 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 28) 16 28:=by decide +kernel
  have hfast:StrictAtFast (row 16 28) 16 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 28) 16 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 28) 16 28 hvalid hfast

theorem sr16p29:∀ i ∈ List.range 1,StrictCheckAt 16 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 29) 16 29:=by decide +kernel
  have hfast:StrictAtFast (row 16 29) 16 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 29) 16 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 29) 16 29 hvalid hfast

theorem sr16p30:∀ i ∈ List.range 1,StrictCheckAt 16 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 30) 16 30:=by decide +kernel
  have hfast:StrictAtFast (row 16 30) 16 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 30) 16 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 30) 16 30 hvalid hfast

theorem sr16p31:∀ i ∈ List.range 1,StrictCheckAt 16 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 31) 16 31:=by decide +kernel
  have hfast:StrictAtFast (row 16 31) 16 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 31) 16 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 31) 16 31 hvalid hfast

theorem sr16p32:∀ i ∈ List.range 1,StrictCheckAt 16 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 32) 16 32:=by decide +kernel
  have hfast:StrictAtFast (row 16 32) 16 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 32) 16 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 32) 16 32 hvalid hfast

theorem sr16p33:∀ i ∈ List.range 1,StrictCheckAt 16 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 33) 16 33:=by decide +kernel
  have hfast:StrictAtFast (row 16 33) 16 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 33) 16 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 33) 16 33 hvalid hfast

theorem sr16p34:∀ i ∈ List.range 1,StrictCheckAt 16 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 34) 16 34:=by decide +kernel
  have hfast:StrictAtFast (row 16 34) 16 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 34) 16 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 34) 16 34 hvalid hfast

theorem sr16p35:∀ i ∈ List.range 1,StrictCheckAt 16 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 35) 16 35:=by decide +kernel
  have hfast:StrictAtFast (row 16 35) 16 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 35) 16 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 35) 16 35 hvalid hfast

theorem sr16p36:∀ i ∈ List.range 1,StrictCheckAt 16 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 36) 16 36:=by decide +kernel
  have hfast:StrictAtFast (row 16 36) 16 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 36) 16 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 36) 16 36 hvalid hfast

theorem sr16p37:∀ i ∈ List.range 1,StrictCheckAt 16 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 37) 16 37:=by decide +kernel
  have hfast:StrictAtFast (row 16 37) 16 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 37) 16 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 37) 16 37 hvalid hfast

theorem sr16p38:∀ i ∈ List.range 1,StrictCheckAt 16 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 38) 16 38:=by decide +kernel
  have hfast:StrictAtFast (row 16 38) 16 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 38) 16 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 38) 16 38 hvalid hfast

theorem sr16p39:∀ i ∈ List.range 1,StrictCheckAt 16 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 39) 16 39:=by decide +kernel
  have hfast:StrictAtFast (row 16 39) 16 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 39) 16 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 39) 16 39 hvalid hfast

theorem sr16p40:∀ i ∈ List.range 1,StrictCheckAt 16 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 40) 16 40:=by decide +kernel
  have hfast:StrictAtFast (row 16 40) 16 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 40) 16 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 40) 16 40 hvalid hfast

theorem sr16p41:∀ i ∈ List.range 1,StrictCheckAt 16 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 41) 16 41:=by decide +kernel
  have hfast:StrictAtFast (row 16 41) 16 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 41) 16 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 41) 16 41 hvalid hfast

theorem sr16p42:∀ i ∈ List.range 1,StrictCheckAt 16 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 42) 16 42:=by decide +kernel
  have hfast:StrictAtFast (row 16 42) 16 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 42) 16 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 42) 16 42 hvalid hfast

theorem sr16p43:∀ i ∈ List.range 1,StrictCheckAt 16 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 43) 16 43:=by decide +kernel
  have hfast:StrictAtFast (row 16 43) 16 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 43) 16 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 43) 16 43 hvalid hfast

theorem sr16p44:∀ i ∈ List.range 1,StrictCheckAt 16 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 44) 16 44:=by decide +kernel
  have hfast:StrictAtFast (row 16 44) 16 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 44) 16 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 44) 16 44 hvalid hfast

theorem sr16p45:∀ i ∈ List.range 1,StrictCheckAt 16 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 45) 16 45:=by decide +kernel
  have hfast:StrictAtFast (row 16 45) 16 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 45) 16 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 45) 16 45 hvalid hfast

theorem sr16p46:∀ i ∈ List.range 1,StrictCheckAt 16 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 46) 16 46:=by decide +kernel
  have hfast:StrictAtFast (row 16 46) 16 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 46) 16 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 46) 16 46 hvalid hfast

theorem sr16p47:∀ i ∈ List.range 1,StrictCheckAt 16 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 47) 16 47:=by decide +kernel
  have hfast:StrictAtFast (row 16 47) 16 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 47) 16 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 47) 16 47 hvalid hfast

theorem sr16p48:∀ i ∈ List.range 1,StrictCheckAt 16 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 48) 16 48:=by decide +kernel
  have hfast:StrictAtFast (row 16 48) 16 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 48) 16 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 48) 16 48 hvalid hfast

theorem sr16p49:∀ i ∈ List.range 1,StrictCheckAt 16 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 49) 16 49:=by decide +kernel
  have hfast:StrictAtFast (row 16 49) 16 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 49) 16 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 49) 16 49 hvalid hfast

theorem sr16p50:∀ i ∈ List.range 1,StrictCheckAt 16 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 50) 16 50:=by decide +kernel
  have hfast:StrictAtFast (row 16 50) 16 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 50) 16 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 50) 16 50 hvalid hfast

theorem sr16p51:∀ i ∈ List.range 1,StrictCheckAt 16 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 51) 16 51:=by decide +kernel
  have hfast:StrictAtFast (row 16 51) 16 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 51) 16 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 51) 16 51 hvalid hfast

theorem sr16p52:∀ i ∈ List.range 1,StrictCheckAt 16 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 52) 16 52:=by decide +kernel
  have hfast:StrictAtFast (row 16 52) 16 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 52) 16 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 52) 16 52 hvalid hfast

theorem sr16p53:∀ i ∈ List.range 1,StrictCheckAt 16 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 53) 16 53:=by decide +kernel
  have hfast:StrictAtFast (row 16 53) 16 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 53) 16 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 53) 16 53 hvalid hfast

theorem sr16p54:∀ i ∈ List.range 1,StrictCheckAt 16 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 54) 16 54:=by decide +kernel
  have hfast:StrictAtFast (row 16 54) 16 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 54) 16 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 54) 16 54 hvalid hfast

theorem sr16p55:∀ i ∈ List.range 1,StrictCheckAt 16 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 55) 16 55:=by decide +kernel
  have hfast:StrictAtFast (row 16 55) 16 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 55) 16 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 55) 16 55 hvalid hfast

theorem sr16p56:∀ i ∈ List.range 1,StrictCheckAt 16 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 56) 16 56:=by decide +kernel
  have hfast:StrictAtFast (row 16 56) 16 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 56) 16 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 56) 16 56 hvalid hfast

theorem sr16p57:∀ i ∈ List.range 1,StrictCheckAt 16 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 57) 16 57:=by decide +kernel
  have hfast:StrictAtFast (row 16 57) 16 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 57) 16 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 57) 16 57 hvalid hfast

theorem sr16p58:∀ i ∈ List.range 1,StrictCheckAt 16 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 58) 16 58:=by decide +kernel
  have hfast:StrictAtFast (row 16 58) 16 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 58) 16 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 58) 16 58 hvalid hfast

theorem sr16p59:∀ i ∈ List.range 1,StrictCheckAt 16 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 59) 16 59:=by decide +kernel
  have hfast:StrictAtFast (row 16 59) 16 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 59) 16 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 59) 16 59 hvalid hfast

theorem sr16p60:∀ i ∈ List.range 1,StrictCheckAt 16 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 60) 16 60:=by decide +kernel
  have hfast:StrictAtFast (row 16 60) 16 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 60) 16 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 60) 16 60 hvalid hfast

theorem sr16p61:∀ i ∈ List.range 1,StrictCheckAt 16 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 61) 16 61:=by decide +kernel
  have hfast:StrictAtFast (row 16 61) 16 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 61) 16 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 61) 16 61 hvalid hfast

theorem sr16p62:∀ i ∈ List.range 1,StrictCheckAt 16 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 62) 16 62:=by decide +kernel
  have hfast:StrictAtFast (row 16 62) 16 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 62) 16 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 62) 16 62 hvalid hfast

theorem sr16p63:∀ i ∈ List.range 1,StrictCheckAt 16 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 63) 16 63:=by decide +kernel
  have hfast:StrictAtFast (row 16 63) 16 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 63) 16 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 63) 16 63 hvalid hfast

theorem sr16p64:∀ i ∈ List.range 1,StrictCheckAt 16 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 64) 16 64:=by decide +kernel
  have hfast:StrictAtFast (row 16 64) 16 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 64) 16 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 64) 16 64 hvalid hfast

theorem sr16p65:∀ i ∈ List.range 1,StrictCheckAt 16 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 65) 16 65:=by decide +kernel
  have hfast:StrictAtFast (row 16 65) 16 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 65) 16 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 65) 16 65 hvalid hfast

theorem sr16p66:∀ i ∈ List.range 1,StrictCheckAt 16 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 66) 16 66:=by decide +kernel
  have hfast:StrictAtFast (row 16 66) 16 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 66) 16 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 66) 16 66 hvalid hfast

theorem sr16p67:∀ i ∈ List.range 1,StrictCheckAt 16 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 67) 16 67:=by decide +kernel
  have hfast:StrictAtFast (row 16 67) 16 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 67) 16 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 67) 16 67 hvalid hfast

theorem sr16p68:∀ i ∈ List.range 1,StrictCheckAt 16 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 68) 16 68:=by decide +kernel
  have hfast:StrictAtFast (row 16 68) 16 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 68) 16 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 68) 16 68 hvalid hfast

theorem sr16p69:∀ i ∈ List.range 1,StrictCheckAt 16 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 69) 16 69:=by decide +kernel
  have hfast:StrictAtFast (row 16 69) 16 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 69) 16 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 69) 16 69 hvalid hfast

theorem sr16p70:∀ i ∈ List.range 1,StrictCheckAt 16 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 70) 16 70:=by decide +kernel
  have hfast:StrictAtFast (row 16 70) 16 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 70) 16 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 70) 16 70 hvalid hfast

theorem sr16p71:∀ i ∈ List.range 1,StrictCheckAt 16 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 71) 16 71:=by decide +kernel
  have hfast:StrictAtFast (row 16 71) 16 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 71) 16 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 71) 16 71 hvalid hfast

theorem sr16p72:∀ i ∈ List.range 1,StrictCheckAt 16 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 72) 16 72:=by decide +kernel
  have hfast:StrictAtFast (row 16 72) 16 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 72) 16 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 72) 16 72 hvalid hfast

theorem sr16p73:∀ i ∈ List.range 1,StrictCheckAt 16 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 73) 16 73:=by decide +kernel
  have hfast:StrictAtFast (row 16 73) 16 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 73) 16 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 73) 16 73 hvalid hfast

theorem sr16p74:∀ i ∈ List.range 1,StrictCheckAt 16 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 74) 16 74:=by decide +kernel
  have hfast:StrictAtFast (row 16 74) 16 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 74) 16 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 74) 16 74 hvalid hfast

theorem sr16p75:∀ i ∈ List.range 1,StrictCheckAt 16 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 75) 16 75:=by decide +kernel
  have hfast:StrictAtFast (row 16 75) 16 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 75) 16 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 75) 16 75 hvalid hfast

theorem sr16p76:∀ i ∈ List.range 1,StrictCheckAt 16 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 76) 16 76:=by decide +kernel
  have hfast:StrictAtFast (row 16 76) 16 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 76) 16 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 76) 16 76 hvalid hfast

theorem sr16p77:∀ i ∈ List.range 1,StrictCheckAt 16 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 77) 16 77:=by decide +kernel
  have hfast:StrictAtFast (row 16 77) 16 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 77) 16 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 77) 16 77 hvalid hfast

theorem sr16p78:∀ i ∈ List.range 1,StrictCheckAt 16 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 78) 16 78:=by decide +kernel
  have hfast:StrictAtFast (row 16 78) 16 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 78) 16 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 78) 16 78 hvalid hfast

theorem sr16p79:∀ i ∈ List.range 1,StrictCheckAt 16 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 79) 16 79:=by decide +kernel
  have hfast:StrictAtFast (row 16 79) 16 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 79) 16 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 79) 16 79 hvalid hfast

theorem sr16p80:∀ i ∈ List.range 1,StrictCheckAt 16 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 80) 16 80:=by decide +kernel
  have hfast:StrictAtFast (row 16 80) 16 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 80) 16 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 80) 16 80 hvalid hfast

theorem sr16p81:∀ i ∈ List.range 1,StrictCheckAt 16 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 81) 16 81:=by decide +kernel
  have hfast:StrictAtFast (row 16 81) 16 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 81) 16 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 81) 16 81 hvalid hfast

theorem sr16p82:∀ i ∈ List.range 1,StrictCheckAt 16 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 82) 16 82:=by decide +kernel
  have hfast:StrictAtFast (row 16 82) 16 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 82) 16 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 82) 16 82 hvalid hfast

theorem sr16p83:∀ i ∈ List.range 1,StrictCheckAt 16 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 83) 16 83:=by decide +kernel
  have hfast:StrictAtFast (row 16 83) 16 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 83) 16 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 83) 16 83 hvalid hfast

theorem sr16p84:∀ i ∈ List.range 1,StrictCheckAt 16 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 84) 16 84:=by decide +kernel
  have hfast:StrictAtFast (row 16 84) 16 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 84) 16 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 84) 16 84 hvalid hfast

theorem sr16p85:∀ i ∈ List.range 1,StrictCheckAt 16 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 85) 16 85:=by decide +kernel
  have hfast:StrictAtFast (row 16 85) 16 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 85) 16 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 85) 16 85 hvalid hfast

theorem sr16p86:∀ i ∈ List.range 1,StrictCheckAt 16 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 86) 16 86:=by decide +kernel
  have hfast:StrictAtFast (row 16 86) 16 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 86) 16 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 86) 16 86 hvalid hfast

theorem sr16p87:∀ i ∈ List.range 1,StrictCheckAt 16 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 87) 16 87:=by decide +kernel
  have hfast:StrictAtFast (row 16 87) 16 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 87) 16 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 87) 16 87 hvalid hfast

theorem sr16p88:∀ i ∈ List.range 1,StrictCheckAt 16 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 88) 16 88:=by decide +kernel
  have hfast:StrictAtFast (row 16 88) 16 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 88) 16 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 88) 16 88 hvalid hfast

theorem sr16p89:∀ i ∈ List.range 1,StrictCheckAt 16 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 89) 16 89:=by decide +kernel
  have hfast:StrictAtFast (row 16 89) 16 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 89) 16 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 89) 16 89 hvalid hfast

theorem sr16p90:∀ i ∈ List.range 1,StrictCheckAt 16 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 90) 16 90:=by decide +kernel
  have hfast:StrictAtFast (row 16 90) 16 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 90) 16 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 90) 16 90 hvalid hfast

theorem sr16p91:∀ i ∈ List.range 1,StrictCheckAt 16 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 91) 16 91:=by decide +kernel
  have hfast:StrictAtFast (row 16 91) 16 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 91) 16 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 91) 16 91 hvalid hfast

theorem sr16p92:∀ i ∈ List.range 1,StrictCheckAt 16 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 92) 16 92:=by decide +kernel
  have hfast:StrictAtFast (row 16 92) 16 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 92) 16 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 92) 16 92 hvalid hfast

theorem sr16p93:∀ i ∈ List.range 1,StrictCheckAt 16 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 93) 16 93:=by decide +kernel
  have hfast:StrictAtFast (row 16 93) 16 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 93) 16 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 93) 16 93 hvalid hfast

theorem sr16p94:∀ i ∈ List.range 1,StrictCheckAt 16 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 94) 16 94:=by decide +kernel
  have hfast:StrictAtFast (row 16 94) 16 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 94) 16 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 94) 16 94 hvalid hfast

theorem sr16p95:∀ i ∈ List.range 1,StrictCheckAt 16 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 95) 16 95:=by decide +kernel
  have hfast:StrictAtFast (row 16 95) 16 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 95) 16 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 95) 16 95 hvalid hfast

theorem sr16p96:∀ i ∈ List.range 1,StrictCheckAt 16 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 96) 16 96:=by decide +kernel
  have hfast:StrictAtFast (row 16 96) 16 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 96) 16 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 96) 16 96 hvalid hfast

theorem sr16p97:∀ i ∈ List.range 1,StrictCheckAt 16 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 97) 16 97:=by decide +kernel
  have hfast:StrictAtFast (row 16 97) 16 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 97) 16 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 97) 16 97 hvalid hfast

theorem sr16p98:∀ i ∈ List.range 1,StrictCheckAt 16 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 98) 16 98:=by decide +kernel
  have hfast:StrictAtFast (row 16 98) 16 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 98) 16 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 98) 16 98 hvalid hfast

theorem sr16p99:∀ i ∈ List.range 1,StrictCheckAt 16 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 99) 16 99:=by decide +kernel
  have hfast:StrictAtFast (row 16 99) 16 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 99) 16 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 99) 16 99 hvalid hfast

theorem sr16p100:∀ i ∈ List.range 1,StrictCheckAt 16 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 100) 16 100:=by decide +kernel
  have hfast:StrictAtFast (row 16 100) 16 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 100) 16 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 100) 16 100 hvalid hfast

theorem sr16p101:∀ i ∈ List.range 1,StrictCheckAt 16 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 101) 16 101:=by decide +kernel
  have hfast:StrictAtFast (row 16 101) 16 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 101) 16 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 101) 16 101 hvalid hfast

theorem sr16p102:∀ i ∈ List.range 1,StrictCheckAt 16 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 102) 16 102:=by decide +kernel
  have hfast:StrictAtFast (row 16 102) 16 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 102) 16 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 102) 16 102 hvalid hfast

theorem sr16p103:∀ i ∈ List.range 1,StrictCheckAt 16 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 103) 16 103:=by decide +kernel
  have hfast:StrictAtFast (row 16 103) 16 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 103) 16 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 103) 16 103 hvalid hfast

theorem sr16p104:∀ i ∈ List.range 1,StrictCheckAt 16 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 104) 16 104:=by decide +kernel
  have hfast:StrictAtFast (row 16 104) 16 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 104) 16 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 104) 16 104 hvalid hfast

theorem sr16p105:∀ i ∈ List.range 1,StrictCheckAt 16 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 105) 16 105:=by decide +kernel
  have hfast:StrictAtFast (row 16 105) 16 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 105) 16 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 105) 16 105 hvalid hfast

theorem sr16p106:∀ i ∈ List.range 1,StrictCheckAt 16 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 106) 16 106:=by decide +kernel
  have hfast:StrictAtFast (row 16 106) 16 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 106) 16 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 106) 16 106 hvalid hfast

theorem sr16p107:∀ i ∈ List.range 1,StrictCheckAt 16 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 107) 16 107:=by decide +kernel
  have hfast:StrictAtFast (row 16 107) 16 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 107) 16 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 107) 16 107 hvalid hfast

theorem sr16p108:∀ i ∈ List.range 1,StrictCheckAt 16 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 108) 16 108:=by decide +kernel
  have hfast:StrictAtFast (row 16 108) 16 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 108) 16 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 108) 16 108 hvalid hfast

theorem sr16p109:∀ i ∈ List.range 1,StrictCheckAt 16 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 109) 16 109:=by decide +kernel
  have hfast:StrictAtFast (row 16 109) 16 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 109) 16 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 109) 16 109 hvalid hfast

theorem sr16p110:∀ i ∈ List.range 1,StrictCheckAt 16 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 110) 16 110:=by decide +kernel
  have hfast:StrictAtFast (row 16 110) 16 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 110) 16 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 110) 16 110 hvalid hfast

theorem sr16p111:∀ i ∈ List.range 1,StrictCheckAt 16 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 111) 16 111:=by decide +kernel
  have hfast:StrictAtFast (row 16 111) 16 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 111) 16 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 111) 16 111 hvalid hfast

theorem sr16p112:∀ i ∈ List.range 1,StrictCheckAt 16 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 112) 16 112:=by decide +kernel
  have hfast:StrictAtFast (row 16 112) 16 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 112) 16 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 112) 16 112 hvalid hfast

theorem sr16p113:∀ i ∈ List.range 1,StrictCheckAt 16 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 113) 16 113:=by decide +kernel
  have hfast:StrictAtFast (row 16 113) 16 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 113) 16 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 113) 16 113 hvalid hfast

theorem sr16p114:∀ i ∈ List.range 1,StrictCheckAt 16 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 114) 16 114:=by decide +kernel
  have hfast:StrictAtFast (row 16 114) 16 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 114) 16 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 114) 16 114 hvalid hfast

theorem sr16p115:∀ i ∈ List.range 1,StrictCheckAt 16 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 115) 16 115:=by decide +kernel
  have hfast:StrictAtFast (row 16 115) 16 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 115) 16 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 115) 16 115 hvalid hfast

theorem sr16p116:∀ i ∈ List.range 1,StrictCheckAt 16 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 116) 16 116:=by decide +kernel
  have hfast:StrictAtFast (row 16 116) 16 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 116) 16 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 116) 16 116 hvalid hfast

theorem sr16p117:∀ i ∈ List.range 1,StrictCheckAt 16 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 117) 16 117:=by decide +kernel
  have hfast:StrictAtFast (row 16 117) 16 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 117) 16 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 117) 16 117 hvalid hfast

theorem sr16p118:∀ i ∈ List.range 1,StrictCheckAt 16 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 118) 16 118:=by decide +kernel
  have hfast:StrictAtFast (row 16 118) 16 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 118) 16 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 118) 16 118 hvalid hfast

theorem sr16p119:∀ i ∈ List.range 1,StrictCheckAt 16 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 119) 16 119:=by decide +kernel
  have hfast:StrictAtFast (row 16 119) 16 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 119) 16 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 119) 16 119 hvalid hfast

theorem sr16p120:∀ i ∈ List.range 1,StrictCheckAt 16 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 120) 16 120:=by decide +kernel
  have hfast:StrictAtFast (row 16 120) 16 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 120) 16 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 120) 16 120 hvalid hfast

theorem sr16p121:∀ i ∈ List.range 1,StrictCheckAt 16 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 121) 16 121:=by decide +kernel
  have hfast:StrictAtFast (row 16 121) 16 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 121) 16 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 121) 16 121 hvalid hfast

theorem sr16p122:∀ i ∈ List.range 1,StrictCheckAt 16 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 122) 16 122:=by decide +kernel
  have hfast:StrictAtFast (row 16 122) 16 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 122) 16 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 122) 16 122 hvalid hfast

theorem sr16p123:∀ i ∈ List.range 1,StrictCheckAt 16 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 123) 16 123:=by decide +kernel
  have hfast:StrictAtFast (row 16 123) 16 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 123) 16 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 123) 16 123 hvalid hfast

theorem sr16p124:∀ i ∈ List.range 1,StrictCheckAt 16 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 124) 16 124:=by decide +kernel
  have hfast:StrictAtFast (row 16 124) 16 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 124) 16 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 124) 16 124 hvalid hfast

theorem sr16p125:∀ i ∈ List.range 1,StrictCheckAt 16 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 125) 16 125:=by decide +kernel
  have hfast:StrictAtFast (row 16 125) 16 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 125) 16 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 125) 16 125 hvalid hfast

theorem sr16p126:∀ i ∈ List.range 1,StrictCheckAt 16 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 126) 16 126:=by decide +kernel
  have hfast:StrictAtFast (row 16 126) 16 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 126) 16 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 126) 16 126 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
