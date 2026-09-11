import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr20p0:∀ i ∈ List.range 8,CorrectAt 20 (0+i):=by decide +kernel

theorem cr20p1:∀ i ∈ List.range 8,CorrectAt 20 (8+i):=by decide +kernel

theorem cr20p2:∀ i ∈ List.range 8,CorrectAt 20 (16+i):=by decide +kernel

theorem cr20p3:∀ i ∈ List.range 8,CorrectAt 20 (24+i):=by decide +kernel

theorem cr20p4:∀ i ∈ List.range 8,CorrectAt 20 (32+i):=by decide +kernel

theorem cr20p5:∀ i ∈ List.range 8,CorrectAt 20 (40+i):=by decide +kernel

theorem cr20p6:∀ i ∈ List.range 8,CorrectAt 20 (48+i):=by decide +kernel

theorem cr20p7:∀ i ∈ List.range 8,CorrectAt 20 (56+i):=by decide +kernel

theorem cr20p8:∀ i ∈ List.range 8,CorrectAt 20 (64+i):=by decide +kernel

theorem cr20p9:∀ i ∈ List.range 8,CorrectAt 20 (72+i):=by decide +kernel

theorem cr20p10:∀ i ∈ List.range 8,CorrectAt 20 (80+i):=by decide +kernel

theorem cr20p11:∀ i ∈ List.range 8,CorrectAt 20 (88+i):=by decide +kernel

theorem cr20p12:∀ i ∈ List.range 8,CorrectAt 20 (96+i):=by decide +kernel

theorem cr20p13:∀ i ∈ List.range 8,CorrectAt 20 (104+i):=by decide +kernel

theorem cr20p14:∀ i ∈ List.range 8,CorrectAt 20 (112+i):=by decide +kernel

theorem cr20p15:∀ i ∈ List.range 3,CorrectAt 20 (120+i):=by decide +kernel

theorem sr20p0:∀ i ∈ List.range 1,StrictCheckAt 20 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 0) 20 0:=by decide +kernel
  have hfast:StrictAtFast (row 20 0) 20 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 0) 20 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 0) 20 0 hvalid hfast

theorem sr20p1:∀ i ∈ List.range 1,StrictCheckAt 20 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 1) 20 1:=by decide +kernel
  have hfast:StrictAtFast (row 20 1) 20 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 1) 20 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 1) 20 1 hvalid hfast

theorem sr20p2:∀ i ∈ List.range 1,StrictCheckAt 20 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 2) 20 2:=by decide +kernel
  have hfast:StrictAtFast (row 20 2) 20 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 2) 20 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 2) 20 2 hvalid hfast

theorem sr20p3:∀ i ∈ List.range 1,StrictCheckAt 20 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 3) 20 3:=by decide +kernel
  have hfast:StrictAtFast (row 20 3) 20 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 3) 20 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 3) 20 3 hvalid hfast

theorem sr20p4:∀ i ∈ List.range 1,StrictCheckAt 20 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 4) 20 4:=by decide +kernel
  have hfast:StrictAtFast (row 20 4) 20 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 4) 20 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 4) 20 4 hvalid hfast

theorem sr20p5:∀ i ∈ List.range 1,StrictCheckAt 20 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 5) 20 5:=by decide +kernel
  have hfast:StrictAtFast (row 20 5) 20 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 5) 20 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 5) 20 5 hvalid hfast

theorem sr20p6:∀ i ∈ List.range 1,StrictCheckAt 20 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 6) 20 6:=by decide +kernel
  have hfast:StrictAtFast (row 20 6) 20 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 6) 20 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 6) 20 6 hvalid hfast

theorem sr20p7:∀ i ∈ List.range 1,StrictCheckAt 20 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 7) 20 7:=by decide +kernel
  have hfast:StrictAtFast (row 20 7) 20 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 7) 20 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 7) 20 7 hvalid hfast

theorem sr20p8:∀ i ∈ List.range 1,StrictCheckAt 20 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 8) 20 8:=by decide +kernel
  have hfast:StrictAtFast (row 20 8) 20 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 8) 20 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 8) 20 8 hvalid hfast

theorem sr20p9:∀ i ∈ List.range 1,StrictCheckAt 20 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 9) 20 9:=by decide +kernel
  have hfast:StrictAtFast (row 20 9) 20 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 9) 20 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 9) 20 9 hvalid hfast

theorem sr20p10:∀ i ∈ List.range 1,StrictCheckAt 20 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 10) 20 10:=by decide +kernel
  have hfast:StrictAtFast (row 20 10) 20 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 10) 20 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 10) 20 10 hvalid hfast

theorem sr20p11:∀ i ∈ List.range 1,StrictCheckAt 20 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 11) 20 11:=by decide +kernel
  have hfast:StrictAtFast (row 20 11) 20 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 11) 20 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 11) 20 11 hvalid hfast

theorem sr20p12:∀ i ∈ List.range 1,StrictCheckAt 20 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 12) 20 12:=by decide +kernel
  have hfast:StrictAtFast (row 20 12) 20 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 12) 20 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 12) 20 12 hvalid hfast

theorem sr20p13:∀ i ∈ List.range 1,StrictCheckAt 20 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 13) 20 13:=by decide +kernel
  have hfast:StrictAtFast (row 20 13) 20 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 13) 20 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 13) 20 13 hvalid hfast

theorem sr20p14:∀ i ∈ List.range 1,StrictCheckAt 20 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 14) 20 14:=by decide +kernel
  have hfast:StrictAtFast (row 20 14) 20 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 14) 20 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 14) 20 14 hvalid hfast

theorem sr20p15:∀ i ∈ List.range 1,StrictCheckAt 20 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 15) 20 15:=by decide +kernel
  have hfast:StrictAtFast (row 20 15) 20 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 15) 20 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 15) 20 15 hvalid hfast

theorem sr20p16:∀ i ∈ List.range 1,StrictCheckAt 20 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 16) 20 16:=by decide +kernel
  have hfast:StrictAtFast (row 20 16) 20 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 16) 20 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 16) 20 16 hvalid hfast

theorem sr20p17:∀ i ∈ List.range 1,StrictCheckAt 20 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 17) 20 17:=by decide +kernel
  have hfast:StrictAtFast (row 20 17) 20 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 17) 20 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 17) 20 17 hvalid hfast

theorem sr20p18:∀ i ∈ List.range 1,StrictCheckAt 20 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 18) 20 18:=by decide +kernel
  have hfast:StrictAtFast (row 20 18) 20 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 18) 20 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 18) 20 18 hvalid hfast

theorem sr20p19:∀ i ∈ List.range 1,StrictCheckAt 20 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 19) 20 19:=by decide +kernel
  have hfast:StrictAtFast (row 20 19) 20 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 19) 20 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 19) 20 19 hvalid hfast

theorem sr20p20:∀ i ∈ List.range 1,StrictCheckAt 20 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 20) 20 20:=by decide +kernel
  have hfast:StrictAtFast (row 20 20) 20 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 20) 20 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 20) 20 20 hvalid hfast

theorem sr20p21:∀ i ∈ List.range 1,StrictCheckAt 20 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 21) 20 21:=by decide +kernel
  have hfast:StrictAtFast (row 20 21) 20 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 21) 20 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 21) 20 21 hvalid hfast

theorem sr20p22:∀ i ∈ List.range 1,StrictCheckAt 20 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 22) 20 22:=by decide +kernel
  have hfast:StrictAtFast (row 20 22) 20 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 22) 20 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 22) 20 22 hvalid hfast

theorem sr20p23:∀ i ∈ List.range 1,StrictCheckAt 20 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 23) 20 23:=by decide +kernel
  have hfast:StrictAtFast (row 20 23) 20 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 23) 20 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 23) 20 23 hvalid hfast

theorem sr20p24:∀ i ∈ List.range 1,StrictCheckAt 20 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 24) 20 24:=by decide +kernel
  have hfast:StrictAtFast (row 20 24) 20 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 24) 20 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 24) 20 24 hvalid hfast

theorem sr20p25:∀ i ∈ List.range 1,StrictCheckAt 20 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 25) 20 25:=by decide +kernel
  have hfast:StrictAtFast (row 20 25) 20 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 25) 20 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 25) 20 25 hvalid hfast

theorem sr20p26:∀ i ∈ List.range 1,StrictCheckAt 20 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 26) 20 26:=by decide +kernel
  have hfast:StrictAtFast (row 20 26) 20 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 26) 20 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 26) 20 26 hvalid hfast

theorem sr20p27:∀ i ∈ List.range 1,StrictCheckAt 20 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 27) 20 27:=by decide +kernel
  have hfast:StrictAtFast (row 20 27) 20 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 27) 20 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 27) 20 27 hvalid hfast

theorem sr20p28:∀ i ∈ List.range 1,StrictCheckAt 20 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 28) 20 28:=by decide +kernel
  have hfast:StrictAtFast (row 20 28) 20 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 28) 20 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 28) 20 28 hvalid hfast

theorem sr20p29:∀ i ∈ List.range 1,StrictCheckAt 20 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 29) 20 29:=by decide +kernel
  have hfast:StrictAtFast (row 20 29) 20 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 29) 20 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 29) 20 29 hvalid hfast

theorem sr20p30:∀ i ∈ List.range 1,StrictCheckAt 20 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 30) 20 30:=by decide +kernel
  have hfast:StrictAtFast (row 20 30) 20 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 30) 20 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 30) 20 30 hvalid hfast

theorem sr20p31:∀ i ∈ List.range 1,StrictCheckAt 20 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 31) 20 31:=by decide +kernel
  have hfast:StrictAtFast (row 20 31) 20 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 31) 20 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 31) 20 31 hvalid hfast

theorem sr20p32:∀ i ∈ List.range 1,StrictCheckAt 20 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 32) 20 32:=by decide +kernel
  have hfast:StrictAtFast (row 20 32) 20 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 32) 20 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 32) 20 32 hvalid hfast

theorem sr20p33:∀ i ∈ List.range 1,StrictCheckAt 20 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 33) 20 33:=by decide +kernel
  have hfast:StrictAtFast (row 20 33) 20 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 33) 20 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 33) 20 33 hvalid hfast

theorem sr20p34:∀ i ∈ List.range 1,StrictCheckAt 20 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 34) 20 34:=by decide +kernel
  have hfast:StrictAtFast (row 20 34) 20 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 34) 20 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 34) 20 34 hvalid hfast

theorem sr20p35:∀ i ∈ List.range 1,StrictCheckAt 20 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 35) 20 35:=by decide +kernel
  have hfast:StrictAtFast (row 20 35) 20 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 35) 20 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 35) 20 35 hvalid hfast

theorem sr20p36:∀ i ∈ List.range 1,StrictCheckAt 20 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 36) 20 36:=by decide +kernel
  have hfast:StrictAtFast (row 20 36) 20 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 36) 20 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 36) 20 36 hvalid hfast

theorem sr20p37:∀ i ∈ List.range 1,StrictCheckAt 20 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 37) 20 37:=by decide +kernel
  have hfast:StrictAtFast (row 20 37) 20 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 37) 20 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 37) 20 37 hvalid hfast

theorem sr20p38:∀ i ∈ List.range 1,StrictCheckAt 20 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 38) 20 38:=by decide +kernel
  have hfast:StrictAtFast (row 20 38) 20 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 38) 20 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 38) 20 38 hvalid hfast

theorem sr20p39:∀ i ∈ List.range 1,StrictCheckAt 20 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 39) 20 39:=by decide +kernel
  have hfast:StrictAtFast (row 20 39) 20 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 39) 20 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 39) 20 39 hvalid hfast

theorem sr20p40:∀ i ∈ List.range 1,StrictCheckAt 20 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 40) 20 40:=by decide +kernel
  have hfast:StrictAtFast (row 20 40) 20 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 40) 20 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 40) 20 40 hvalid hfast

theorem sr20p41:∀ i ∈ List.range 1,StrictCheckAt 20 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 41) 20 41:=by decide +kernel
  have hfast:StrictAtFast (row 20 41) 20 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 41) 20 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 41) 20 41 hvalid hfast

theorem sr20p42:∀ i ∈ List.range 1,StrictCheckAt 20 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 42) 20 42:=by decide +kernel
  have hfast:StrictAtFast (row 20 42) 20 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 42) 20 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 42) 20 42 hvalid hfast

theorem sr20p43:∀ i ∈ List.range 1,StrictCheckAt 20 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 43) 20 43:=by decide +kernel
  have hfast:StrictAtFast (row 20 43) 20 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 43) 20 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 43) 20 43 hvalid hfast

theorem sr20p44:∀ i ∈ List.range 1,StrictCheckAt 20 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 44) 20 44:=by decide +kernel
  have hfast:StrictAtFast (row 20 44) 20 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 44) 20 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 44) 20 44 hvalid hfast

theorem sr20p45:∀ i ∈ List.range 1,StrictCheckAt 20 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 45) 20 45:=by decide +kernel
  have hfast:StrictAtFast (row 20 45) 20 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 45) 20 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 45) 20 45 hvalid hfast

theorem sr20p46:∀ i ∈ List.range 1,StrictCheckAt 20 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 46) 20 46:=by decide +kernel
  have hfast:StrictAtFast (row 20 46) 20 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 46) 20 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 46) 20 46 hvalid hfast

theorem sr20p47:∀ i ∈ List.range 1,StrictCheckAt 20 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 47) 20 47:=by decide +kernel
  have hfast:StrictAtFast (row 20 47) 20 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 47) 20 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 47) 20 47 hvalid hfast

theorem sr20p48:∀ i ∈ List.range 1,StrictCheckAt 20 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 48) 20 48:=by decide +kernel
  have hfast:StrictAtFast (row 20 48) 20 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 48) 20 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 48) 20 48 hvalid hfast

theorem sr20p49:∀ i ∈ List.range 1,StrictCheckAt 20 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 49) 20 49:=by decide +kernel
  have hfast:StrictAtFast (row 20 49) 20 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 49) 20 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 49) 20 49 hvalid hfast

theorem sr20p50:∀ i ∈ List.range 1,StrictCheckAt 20 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 50) 20 50:=by decide +kernel
  have hfast:StrictAtFast (row 20 50) 20 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 50) 20 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 50) 20 50 hvalid hfast

theorem sr20p51:∀ i ∈ List.range 1,StrictCheckAt 20 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 51) 20 51:=by decide +kernel
  have hfast:StrictAtFast (row 20 51) 20 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 51) 20 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 51) 20 51 hvalid hfast

theorem sr20p52:∀ i ∈ List.range 1,StrictCheckAt 20 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 52) 20 52:=by decide +kernel
  have hfast:StrictAtFast (row 20 52) 20 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 52) 20 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 52) 20 52 hvalid hfast

theorem sr20p53:∀ i ∈ List.range 1,StrictCheckAt 20 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 53) 20 53:=by decide +kernel
  have hfast:StrictAtFast (row 20 53) 20 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 53) 20 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 53) 20 53 hvalid hfast

theorem sr20p54:∀ i ∈ List.range 1,StrictCheckAt 20 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 54) 20 54:=by decide +kernel
  have hfast:StrictAtFast (row 20 54) 20 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 54) 20 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 54) 20 54 hvalid hfast

theorem sr20p55:∀ i ∈ List.range 1,StrictCheckAt 20 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 55) 20 55:=by decide +kernel
  have hfast:StrictAtFast (row 20 55) 20 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 55) 20 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 55) 20 55 hvalid hfast

theorem sr20p56:∀ i ∈ List.range 1,StrictCheckAt 20 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 56) 20 56:=by decide +kernel
  have hfast:StrictAtFast (row 20 56) 20 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 56) 20 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 56) 20 56 hvalid hfast

theorem sr20p57:∀ i ∈ List.range 1,StrictCheckAt 20 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 57) 20 57:=by decide +kernel
  have hfast:StrictAtFast (row 20 57) 20 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 57) 20 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 57) 20 57 hvalid hfast

theorem sr20p58:∀ i ∈ List.range 1,StrictCheckAt 20 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 58) 20 58:=by decide +kernel
  have hfast:StrictAtFast (row 20 58) 20 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 58) 20 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 58) 20 58 hvalid hfast

theorem sr20p59:∀ i ∈ List.range 1,StrictCheckAt 20 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 59) 20 59:=by decide +kernel
  have hfast:StrictAtFast (row 20 59) 20 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 59) 20 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 59) 20 59 hvalid hfast

theorem sr20p60:∀ i ∈ List.range 1,StrictCheckAt 20 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 60) 20 60:=by decide +kernel
  have hfast:StrictAtFast (row 20 60) 20 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 60) 20 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 60) 20 60 hvalid hfast

theorem sr20p61:∀ i ∈ List.range 1,StrictCheckAt 20 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 61) 20 61:=by decide +kernel
  have hfast:StrictAtFast (row 20 61) 20 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 61) 20 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 61) 20 61 hvalid hfast

theorem sr20p62:∀ i ∈ List.range 1,StrictCheckAt 20 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 62) 20 62:=by decide +kernel
  have hfast:StrictAtFast (row 20 62) 20 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 62) 20 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 62) 20 62 hvalid hfast

theorem sr20p63:∀ i ∈ List.range 1,StrictCheckAt 20 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 63) 20 63:=by decide +kernel
  have hfast:StrictAtFast (row 20 63) 20 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 63) 20 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 63) 20 63 hvalid hfast

theorem sr20p64:∀ i ∈ List.range 1,StrictCheckAt 20 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 64) 20 64:=by decide +kernel
  have hfast:StrictAtFast (row 20 64) 20 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 64) 20 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 64) 20 64 hvalid hfast

theorem sr20p65:∀ i ∈ List.range 1,StrictCheckAt 20 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 65) 20 65:=by decide +kernel
  have hfast:StrictAtFast (row 20 65) 20 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 65) 20 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 65) 20 65 hvalid hfast

theorem sr20p66:∀ i ∈ List.range 1,StrictCheckAt 20 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 66) 20 66:=by decide +kernel
  have hfast:StrictAtFast (row 20 66) 20 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 66) 20 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 66) 20 66 hvalid hfast

theorem sr20p67:∀ i ∈ List.range 1,StrictCheckAt 20 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 67) 20 67:=by decide +kernel
  have hfast:StrictAtFast (row 20 67) 20 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 67) 20 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 67) 20 67 hvalid hfast

theorem sr20p68:∀ i ∈ List.range 1,StrictCheckAt 20 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 68) 20 68:=by decide +kernel
  have hfast:StrictAtFast (row 20 68) 20 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 68) 20 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 68) 20 68 hvalid hfast

theorem sr20p69:∀ i ∈ List.range 1,StrictCheckAt 20 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 69) 20 69:=by decide +kernel
  have hfast:StrictAtFast (row 20 69) 20 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 69) 20 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 69) 20 69 hvalid hfast

theorem sr20p70:∀ i ∈ List.range 1,StrictCheckAt 20 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 70) 20 70:=by decide +kernel
  have hfast:StrictAtFast (row 20 70) 20 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 70) 20 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 70) 20 70 hvalid hfast

theorem sr20p71:∀ i ∈ List.range 1,StrictCheckAt 20 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 71) 20 71:=by decide +kernel
  have hfast:StrictAtFast (row 20 71) 20 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 71) 20 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 71) 20 71 hvalid hfast

theorem sr20p72:∀ i ∈ List.range 1,StrictCheckAt 20 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 72) 20 72:=by decide +kernel
  have hfast:StrictAtFast (row 20 72) 20 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 72) 20 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 72) 20 72 hvalid hfast

theorem sr20p73:∀ i ∈ List.range 1,StrictCheckAt 20 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 73) 20 73:=by decide +kernel
  have hfast:StrictAtFast (row 20 73) 20 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 73) 20 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 73) 20 73 hvalid hfast

theorem sr20p74:∀ i ∈ List.range 1,StrictCheckAt 20 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 74) 20 74:=by decide +kernel
  have hfast:StrictAtFast (row 20 74) 20 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 74) 20 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 74) 20 74 hvalid hfast

theorem sr20p75:∀ i ∈ List.range 1,StrictCheckAt 20 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 75) 20 75:=by decide +kernel
  have hfast:StrictAtFast (row 20 75) 20 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 75) 20 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 75) 20 75 hvalid hfast

theorem sr20p76:∀ i ∈ List.range 1,StrictCheckAt 20 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 76) 20 76:=by decide +kernel
  have hfast:StrictAtFast (row 20 76) 20 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 76) 20 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 76) 20 76 hvalid hfast

theorem sr20p77:∀ i ∈ List.range 1,StrictCheckAt 20 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 77) 20 77:=by decide +kernel
  have hfast:StrictAtFast (row 20 77) 20 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 77) 20 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 77) 20 77 hvalid hfast

theorem sr20p78:∀ i ∈ List.range 1,StrictCheckAt 20 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 78) 20 78:=by decide +kernel
  have hfast:StrictAtFast (row 20 78) 20 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 78) 20 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 78) 20 78 hvalid hfast

theorem sr20p79:∀ i ∈ List.range 1,StrictCheckAt 20 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 79) 20 79:=by decide +kernel
  have hfast:StrictAtFast (row 20 79) 20 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 79) 20 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 79) 20 79 hvalid hfast

theorem sr20p80:∀ i ∈ List.range 1,StrictCheckAt 20 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 80) 20 80:=by decide +kernel
  have hfast:StrictAtFast (row 20 80) 20 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 80) 20 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 80) 20 80 hvalid hfast

theorem sr20p81:∀ i ∈ List.range 1,StrictCheckAt 20 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 81) 20 81:=by decide +kernel
  have hfast:StrictAtFast (row 20 81) 20 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 81) 20 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 81) 20 81 hvalid hfast

theorem sr20p82:∀ i ∈ List.range 1,StrictCheckAt 20 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 82) 20 82:=by decide +kernel
  have hfast:StrictAtFast (row 20 82) 20 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 82) 20 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 82) 20 82 hvalid hfast

theorem sr20p83:∀ i ∈ List.range 1,StrictCheckAt 20 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 83) 20 83:=by decide +kernel
  have hfast:StrictAtFast (row 20 83) 20 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 83) 20 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 83) 20 83 hvalid hfast

theorem sr20p84:∀ i ∈ List.range 1,StrictCheckAt 20 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 84) 20 84:=by decide +kernel
  have hfast:StrictAtFast (row 20 84) 20 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 84) 20 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 84) 20 84 hvalid hfast

theorem sr20p85:∀ i ∈ List.range 1,StrictCheckAt 20 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 85) 20 85:=by decide +kernel
  have hfast:StrictAtFast (row 20 85) 20 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 85) 20 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 85) 20 85 hvalid hfast

theorem sr20p86:∀ i ∈ List.range 1,StrictCheckAt 20 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 86) 20 86:=by decide +kernel
  have hfast:StrictAtFast (row 20 86) 20 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 86) 20 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 86) 20 86 hvalid hfast

theorem sr20p87:∀ i ∈ List.range 1,StrictCheckAt 20 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 87) 20 87:=by decide +kernel
  have hfast:StrictAtFast (row 20 87) 20 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 87) 20 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 87) 20 87 hvalid hfast

theorem sr20p88:∀ i ∈ List.range 1,StrictCheckAt 20 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 88) 20 88:=by decide +kernel
  have hfast:StrictAtFast (row 20 88) 20 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 88) 20 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 88) 20 88 hvalid hfast

theorem sr20p89:∀ i ∈ List.range 1,StrictCheckAt 20 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 89) 20 89:=by decide +kernel
  have hfast:StrictAtFast (row 20 89) 20 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 89) 20 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 89) 20 89 hvalid hfast

theorem sr20p90:∀ i ∈ List.range 1,StrictCheckAt 20 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 90) 20 90:=by decide +kernel
  have hfast:StrictAtFast (row 20 90) 20 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 90) 20 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 90) 20 90 hvalid hfast

theorem sr20p91:∀ i ∈ List.range 1,StrictCheckAt 20 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 91) 20 91:=by decide +kernel
  have hfast:StrictAtFast (row 20 91) 20 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 91) 20 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 91) 20 91 hvalid hfast

theorem sr20p92:∀ i ∈ List.range 1,StrictCheckAt 20 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 92) 20 92:=by decide +kernel
  have hfast:StrictAtFast (row 20 92) 20 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 92) 20 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 92) 20 92 hvalid hfast

theorem sr20p93:∀ i ∈ List.range 1,StrictCheckAt 20 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 93) 20 93:=by decide +kernel
  have hfast:StrictAtFast (row 20 93) 20 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 93) 20 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 93) 20 93 hvalid hfast

theorem sr20p94:∀ i ∈ List.range 1,StrictCheckAt 20 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 94) 20 94:=by decide +kernel
  have hfast:StrictAtFast (row 20 94) 20 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 94) 20 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 94) 20 94 hvalid hfast

theorem sr20p95:∀ i ∈ List.range 1,StrictCheckAt 20 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 95) 20 95:=by decide +kernel
  have hfast:StrictAtFast (row 20 95) 20 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 95) 20 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 95) 20 95 hvalid hfast

theorem sr20p96:∀ i ∈ List.range 1,StrictCheckAt 20 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 96) 20 96:=by decide +kernel
  have hfast:StrictAtFast (row 20 96) 20 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 96) 20 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 96) 20 96 hvalid hfast

theorem sr20p97:∀ i ∈ List.range 1,StrictCheckAt 20 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 97) 20 97:=by decide +kernel
  have hfast:StrictAtFast (row 20 97) 20 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 97) 20 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 97) 20 97 hvalid hfast

theorem sr20p98:∀ i ∈ List.range 1,StrictCheckAt 20 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 98) 20 98:=by decide +kernel
  have hfast:StrictAtFast (row 20 98) 20 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 98) 20 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 98) 20 98 hvalid hfast

theorem sr20p99:∀ i ∈ List.range 1,StrictCheckAt 20 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 99) 20 99:=by decide +kernel
  have hfast:StrictAtFast (row 20 99) 20 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 99) 20 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 99) 20 99 hvalid hfast

theorem sr20p100:∀ i ∈ List.range 1,StrictCheckAt 20 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 100) 20 100:=by decide +kernel
  have hfast:StrictAtFast (row 20 100) 20 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 100) 20 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 100) 20 100 hvalid hfast

theorem sr20p101:∀ i ∈ List.range 1,StrictCheckAt 20 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 101) 20 101:=by decide +kernel
  have hfast:StrictAtFast (row 20 101) 20 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 101) 20 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 101) 20 101 hvalid hfast

theorem sr20p102:∀ i ∈ List.range 1,StrictCheckAt 20 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 102) 20 102:=by decide +kernel
  have hfast:StrictAtFast (row 20 102) 20 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 102) 20 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 102) 20 102 hvalid hfast

theorem sr20p103:∀ i ∈ List.range 1,StrictCheckAt 20 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 103) 20 103:=by decide +kernel
  have hfast:StrictAtFast (row 20 103) 20 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 103) 20 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 103) 20 103 hvalid hfast

theorem sr20p104:∀ i ∈ List.range 1,StrictCheckAt 20 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 104) 20 104:=by decide +kernel
  have hfast:StrictAtFast (row 20 104) 20 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 104) 20 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 104) 20 104 hvalid hfast

theorem sr20p105:∀ i ∈ List.range 1,StrictCheckAt 20 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 105) 20 105:=by decide +kernel
  have hfast:StrictAtFast (row 20 105) 20 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 105) 20 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 105) 20 105 hvalid hfast

theorem sr20p106:∀ i ∈ List.range 1,StrictCheckAt 20 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 106) 20 106:=by decide +kernel
  have hfast:StrictAtFast (row 20 106) 20 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 106) 20 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 106) 20 106 hvalid hfast

theorem sr20p107:∀ i ∈ List.range 1,StrictCheckAt 20 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 107) 20 107:=by decide +kernel
  have hfast:StrictAtFast (row 20 107) 20 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 107) 20 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 107) 20 107 hvalid hfast

theorem sr20p108:∀ i ∈ List.range 1,StrictCheckAt 20 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 108) 20 108:=by decide +kernel
  have hfast:StrictAtFast (row 20 108) 20 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 108) 20 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 108) 20 108 hvalid hfast

theorem sr20p109:∀ i ∈ List.range 1,StrictCheckAt 20 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 109) 20 109:=by decide +kernel
  have hfast:StrictAtFast (row 20 109) 20 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 109) 20 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 109) 20 109 hvalid hfast

theorem sr20p110:∀ i ∈ List.range 1,StrictCheckAt 20 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 110) 20 110:=by decide +kernel
  have hfast:StrictAtFast (row 20 110) 20 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 110) 20 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 110) 20 110 hvalid hfast

theorem sr20p111:∀ i ∈ List.range 1,StrictCheckAt 20 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 111) 20 111:=by decide +kernel
  have hfast:StrictAtFast (row 20 111) 20 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 111) 20 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 111) 20 111 hvalid hfast

theorem sr20p112:∀ i ∈ List.range 1,StrictCheckAt 20 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 112) 20 112:=by decide +kernel
  have hfast:StrictAtFast (row 20 112) 20 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 112) 20 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 112) 20 112 hvalid hfast

theorem sr20p113:∀ i ∈ List.range 1,StrictCheckAt 20 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 113) 20 113:=by decide +kernel
  have hfast:StrictAtFast (row 20 113) 20 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 113) 20 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 113) 20 113 hvalid hfast

theorem sr20p114:∀ i ∈ List.range 1,StrictCheckAt 20 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 114) 20 114:=by decide +kernel
  have hfast:StrictAtFast (row 20 114) 20 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 114) 20 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 114) 20 114 hvalid hfast

theorem sr20p115:∀ i ∈ List.range 1,StrictCheckAt 20 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 115) 20 115:=by decide +kernel
  have hfast:StrictAtFast (row 20 115) 20 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 115) 20 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 115) 20 115 hvalid hfast

theorem sr20p116:∀ i ∈ List.range 1,StrictCheckAt 20 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 116) 20 116:=by decide +kernel
  have hfast:StrictAtFast (row 20 116) 20 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 116) 20 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 116) 20 116 hvalid hfast

theorem sr20p117:∀ i ∈ List.range 1,StrictCheckAt 20 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 117) 20 117:=by decide +kernel
  have hfast:StrictAtFast (row 20 117) 20 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 117) 20 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 117) 20 117 hvalid hfast

theorem sr20p118:∀ i ∈ List.range 1,StrictCheckAt 20 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 118) 20 118:=by decide +kernel
  have hfast:StrictAtFast (row 20 118) 20 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 118) 20 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 118) 20 118 hvalid hfast

theorem sr20p119:∀ i ∈ List.range 1,StrictCheckAt 20 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 119) 20 119:=by decide +kernel
  have hfast:StrictAtFast (row 20 119) 20 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 119) 20 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 119) 20 119 hvalid hfast

theorem sr20p120:∀ i ∈ List.range 1,StrictCheckAt 20 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 120) 20 120:=by decide +kernel
  have hfast:StrictAtFast (row 20 120) 20 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 120) 20 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 120) 20 120 hvalid hfast

theorem sr20p121:∀ i ∈ List.range 1,StrictCheckAt 20 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 121) 20 121:=by decide +kernel
  have hfast:StrictAtFast (row 20 121) 20 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 121) 20 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 121) 20 121 hvalid hfast

theorem sr20p122:∀ i ∈ List.range 1,StrictCheckAt 20 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 122) 20 122:=by decide +kernel
  have hfast:StrictAtFast (row 20 122) 20 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 122) 20 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 122) 20 122 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
