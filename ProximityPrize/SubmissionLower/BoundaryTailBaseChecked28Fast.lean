import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr28p0:∀ i ∈ List.range 8,CorrectAt 28 (0+i):=by decide +kernel

theorem cr28p1:∀ i ∈ List.range 8,CorrectAt 28 (8+i):=by decide +kernel

theorem cr28p2:∀ i ∈ List.range 8,CorrectAt 28 (16+i):=by decide +kernel

theorem cr28p3:∀ i ∈ List.range 8,CorrectAt 28 (24+i):=by decide +kernel

theorem cr28p4:∀ i ∈ List.range 8,CorrectAt 28 (32+i):=by decide +kernel

theorem cr28p5:∀ i ∈ List.range 8,CorrectAt 28 (40+i):=by decide +kernel

theorem cr28p6:∀ i ∈ List.range 8,CorrectAt 28 (48+i):=by decide +kernel

theorem cr28p7:∀ i ∈ List.range 8,CorrectAt 28 (56+i):=by decide +kernel

theorem cr28p8:∀ i ∈ List.range 8,CorrectAt 28 (64+i):=by decide +kernel

theorem cr28p9:∀ i ∈ List.range 8,CorrectAt 28 (72+i):=by decide +kernel

theorem cr28p10:∀ i ∈ List.range 8,CorrectAt 28 (80+i):=by decide +kernel

theorem cr28p11:∀ i ∈ List.range 8,CorrectAt 28 (88+i):=by decide +kernel

theorem cr28p12:∀ i ∈ List.range 8,CorrectAt 28 (96+i):=by decide +kernel

theorem cr28p13:∀ i ∈ List.range 8,CorrectAt 28 (104+i):=by decide +kernel

theorem cr28p14:∀ i ∈ List.range 3,CorrectAt 28 (112+i):=by decide +kernel

theorem sr28p0:∀ i ∈ List.range 1,StrictCheckAt 28 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 0) 28 0:=by decide +kernel
  have hfast:StrictAtFast (row 28 0) 28 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 0) 28 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 0) 28 0 hvalid hfast

theorem sr28p1:∀ i ∈ List.range 1,StrictCheckAt 28 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 1) 28 1:=by decide +kernel
  have hfast:StrictAtFast (row 28 1) 28 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 1) 28 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 1) 28 1 hvalid hfast

theorem sr28p2:∀ i ∈ List.range 1,StrictCheckAt 28 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 2) 28 2:=by decide +kernel
  have hfast:StrictAtFast (row 28 2) 28 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 2) 28 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 2) 28 2 hvalid hfast

theorem sr28p3:∀ i ∈ List.range 1,StrictCheckAt 28 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 3) 28 3:=by decide +kernel
  have hfast:StrictAtFast (row 28 3) 28 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 3) 28 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 3) 28 3 hvalid hfast

theorem sr28p4:∀ i ∈ List.range 1,StrictCheckAt 28 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 4) 28 4:=by decide +kernel
  have hfast:StrictAtFast (row 28 4) 28 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 4) 28 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 4) 28 4 hvalid hfast

theorem sr28p5:∀ i ∈ List.range 1,StrictCheckAt 28 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 5) 28 5:=by decide +kernel
  have hfast:StrictAtFast (row 28 5) 28 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 5) 28 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 5) 28 5 hvalid hfast

theorem sr28p6:∀ i ∈ List.range 1,StrictCheckAt 28 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 6) 28 6:=by decide +kernel
  have hfast:StrictAtFast (row 28 6) 28 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 6) 28 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 6) 28 6 hvalid hfast

theorem sr28p7:∀ i ∈ List.range 1,StrictCheckAt 28 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 7) 28 7:=by decide +kernel
  have hfast:StrictAtFast (row 28 7) 28 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 7) 28 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 7) 28 7 hvalid hfast

theorem sr28p8:∀ i ∈ List.range 1,StrictCheckAt 28 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 8) 28 8:=by decide +kernel
  have hfast:StrictAtFast (row 28 8) 28 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 8) 28 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 8) 28 8 hvalid hfast

theorem sr28p9:∀ i ∈ List.range 1,StrictCheckAt 28 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 9) 28 9:=by decide +kernel
  have hfast:StrictAtFast (row 28 9) 28 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 9) 28 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 9) 28 9 hvalid hfast

theorem sr28p10:∀ i ∈ List.range 1,StrictCheckAt 28 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 10) 28 10:=by decide +kernel
  have hfast:StrictAtFast (row 28 10) 28 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 10) 28 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 10) 28 10 hvalid hfast

theorem sr28p11:∀ i ∈ List.range 1,StrictCheckAt 28 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 11) 28 11:=by decide +kernel
  have hfast:StrictAtFast (row 28 11) 28 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 11) 28 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 11) 28 11 hvalid hfast

theorem sr28p12:∀ i ∈ List.range 1,StrictCheckAt 28 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 12) 28 12:=by decide +kernel
  have hfast:StrictAtFast (row 28 12) 28 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 12) 28 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 12) 28 12 hvalid hfast

theorem sr28p13:∀ i ∈ List.range 1,StrictCheckAt 28 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 13) 28 13:=by decide +kernel
  have hfast:StrictAtFast (row 28 13) 28 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 13) 28 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 13) 28 13 hvalid hfast

theorem sr28p14:∀ i ∈ List.range 1,StrictCheckAt 28 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 14) 28 14:=by decide +kernel
  have hfast:StrictAtFast (row 28 14) 28 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 14) 28 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 14) 28 14 hvalid hfast

theorem sr28p15:∀ i ∈ List.range 1,StrictCheckAt 28 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 15) 28 15:=by decide +kernel
  have hfast:StrictAtFast (row 28 15) 28 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 15) 28 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 15) 28 15 hvalid hfast

theorem sr28p16:∀ i ∈ List.range 1,StrictCheckAt 28 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 16) 28 16:=by decide +kernel
  have hfast:StrictAtFast (row 28 16) 28 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 16) 28 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 16) 28 16 hvalid hfast

theorem sr28p17:∀ i ∈ List.range 1,StrictCheckAt 28 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 17) 28 17:=by decide +kernel
  have hfast:StrictAtFast (row 28 17) 28 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 17) 28 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 17) 28 17 hvalid hfast

theorem sr28p18:∀ i ∈ List.range 1,StrictCheckAt 28 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 18) 28 18:=by decide +kernel
  have hfast:StrictAtFast (row 28 18) 28 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 18) 28 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 18) 28 18 hvalid hfast

theorem sr28p19:∀ i ∈ List.range 1,StrictCheckAt 28 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 19) 28 19:=by decide +kernel
  have hfast:StrictAtFast (row 28 19) 28 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 19) 28 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 19) 28 19 hvalid hfast

theorem sr28p20:∀ i ∈ List.range 1,StrictCheckAt 28 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 20) 28 20:=by decide +kernel
  have hfast:StrictAtFast (row 28 20) 28 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 20) 28 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 20) 28 20 hvalid hfast

theorem sr28p21:∀ i ∈ List.range 1,StrictCheckAt 28 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 21) 28 21:=by decide +kernel
  have hfast:StrictAtFast (row 28 21) 28 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 21) 28 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 21) 28 21 hvalid hfast

theorem sr28p22:∀ i ∈ List.range 1,StrictCheckAt 28 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 22) 28 22:=by decide +kernel
  have hfast:StrictAtFast (row 28 22) 28 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 22) 28 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 22) 28 22 hvalid hfast

theorem sr28p23:∀ i ∈ List.range 1,StrictCheckAt 28 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 23) 28 23:=by decide +kernel
  have hfast:StrictAtFast (row 28 23) 28 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 23) 28 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 23) 28 23 hvalid hfast

theorem sr28p24:∀ i ∈ List.range 1,StrictCheckAt 28 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 24) 28 24:=by decide +kernel
  have hfast:StrictAtFast (row 28 24) 28 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 24) 28 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 24) 28 24 hvalid hfast

theorem sr28p25:∀ i ∈ List.range 1,StrictCheckAt 28 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 25) 28 25:=by decide +kernel
  have hfast:StrictAtFast (row 28 25) 28 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 25) 28 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 25) 28 25 hvalid hfast

theorem sr28p26:∀ i ∈ List.range 1,StrictCheckAt 28 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 26) 28 26:=by decide +kernel
  have hfast:StrictAtFast (row 28 26) 28 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 26) 28 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 26) 28 26 hvalid hfast

theorem sr28p27:∀ i ∈ List.range 1,StrictCheckAt 28 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 27) 28 27:=by decide +kernel
  have hfast:StrictAtFast (row 28 27) 28 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 27) 28 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 27) 28 27 hvalid hfast

theorem sr28p28:∀ i ∈ List.range 1,StrictCheckAt 28 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 28) 28 28:=by decide +kernel
  have hfast:StrictAtFast (row 28 28) 28 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 28) 28 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 28) 28 28 hvalid hfast

theorem sr28p29:∀ i ∈ List.range 1,StrictCheckAt 28 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 29) 28 29:=by decide +kernel
  have hfast:StrictAtFast (row 28 29) 28 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 29) 28 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 29) 28 29 hvalid hfast

theorem sr28p30:∀ i ∈ List.range 1,StrictCheckAt 28 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 30) 28 30:=by decide +kernel
  have hfast:StrictAtFast (row 28 30) 28 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 30) 28 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 30) 28 30 hvalid hfast

theorem sr28p31:∀ i ∈ List.range 1,StrictCheckAt 28 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 31) 28 31:=by decide +kernel
  have hfast:StrictAtFast (row 28 31) 28 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 31) 28 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 31) 28 31 hvalid hfast

theorem sr28p32:∀ i ∈ List.range 1,StrictCheckAt 28 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 32) 28 32:=by decide +kernel
  have hfast:StrictAtFast (row 28 32) 28 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 32) 28 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 32) 28 32 hvalid hfast

theorem sr28p33:∀ i ∈ List.range 1,StrictCheckAt 28 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 33) 28 33:=by decide +kernel
  have hfast:StrictAtFast (row 28 33) 28 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 33) 28 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 33) 28 33 hvalid hfast

theorem sr28p34:∀ i ∈ List.range 1,StrictCheckAt 28 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 34) 28 34:=by decide +kernel
  have hfast:StrictAtFast (row 28 34) 28 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 34) 28 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 34) 28 34 hvalid hfast

theorem sr28p35:∀ i ∈ List.range 1,StrictCheckAt 28 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 35) 28 35:=by decide +kernel
  have hfast:StrictAtFast (row 28 35) 28 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 35) 28 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 35) 28 35 hvalid hfast

theorem sr28p36:∀ i ∈ List.range 1,StrictCheckAt 28 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 36) 28 36:=by decide +kernel
  have hfast:StrictAtFast (row 28 36) 28 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 36) 28 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 36) 28 36 hvalid hfast

theorem sr28p37:∀ i ∈ List.range 1,StrictCheckAt 28 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 37) 28 37:=by decide +kernel
  have hfast:StrictAtFast (row 28 37) 28 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 37) 28 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 37) 28 37 hvalid hfast

theorem sr28p38:∀ i ∈ List.range 1,StrictCheckAt 28 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 38) 28 38:=by decide +kernel
  have hfast:StrictAtFast (row 28 38) 28 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 38) 28 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 38) 28 38 hvalid hfast

theorem sr28p39:∀ i ∈ List.range 1,StrictCheckAt 28 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 39) 28 39:=by decide +kernel
  have hfast:StrictAtFast (row 28 39) 28 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 39) 28 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 39) 28 39 hvalid hfast

theorem sr28p40:∀ i ∈ List.range 1,StrictCheckAt 28 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 40) 28 40:=by decide +kernel
  have hfast:StrictAtFast (row 28 40) 28 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 40) 28 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 40) 28 40 hvalid hfast

theorem sr28p41:∀ i ∈ List.range 1,StrictCheckAt 28 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 41) 28 41:=by decide +kernel
  have hfast:StrictAtFast (row 28 41) 28 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 41) 28 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 41) 28 41 hvalid hfast

theorem sr28p42:∀ i ∈ List.range 1,StrictCheckAt 28 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 42) 28 42:=by decide +kernel
  have hfast:StrictAtFast (row 28 42) 28 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 42) 28 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 42) 28 42 hvalid hfast

theorem sr28p43:∀ i ∈ List.range 1,StrictCheckAt 28 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 43) 28 43:=by decide +kernel
  have hfast:StrictAtFast (row 28 43) 28 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 43) 28 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 43) 28 43 hvalid hfast

theorem sr28p44:∀ i ∈ List.range 1,StrictCheckAt 28 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 44) 28 44:=by decide +kernel
  have hfast:StrictAtFast (row 28 44) 28 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 44) 28 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 44) 28 44 hvalid hfast

theorem sr28p45:∀ i ∈ List.range 1,StrictCheckAt 28 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 45) 28 45:=by decide +kernel
  have hfast:StrictAtFast (row 28 45) 28 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 45) 28 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 45) 28 45 hvalid hfast

theorem sr28p46:∀ i ∈ List.range 1,StrictCheckAt 28 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 46) 28 46:=by decide +kernel
  have hfast:StrictAtFast (row 28 46) 28 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 46) 28 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 46) 28 46 hvalid hfast

theorem sr28p47:∀ i ∈ List.range 1,StrictCheckAt 28 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 47) 28 47:=by decide +kernel
  have hfast:StrictAtFast (row 28 47) 28 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 47) 28 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 47) 28 47 hvalid hfast

theorem sr28p48:∀ i ∈ List.range 1,StrictCheckAt 28 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 48) 28 48:=by decide +kernel
  have hfast:StrictAtFast (row 28 48) 28 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 48) 28 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 48) 28 48 hvalid hfast

theorem sr28p49:∀ i ∈ List.range 1,StrictCheckAt 28 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 49) 28 49:=by decide +kernel
  have hfast:StrictAtFast (row 28 49) 28 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 49) 28 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 49) 28 49 hvalid hfast

theorem sr28p50:∀ i ∈ List.range 1,StrictCheckAt 28 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 50) 28 50:=by decide +kernel
  have hfast:StrictAtFast (row 28 50) 28 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 50) 28 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 50) 28 50 hvalid hfast

theorem sr28p51:∀ i ∈ List.range 1,StrictCheckAt 28 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 51) 28 51:=by decide +kernel
  have hfast:StrictAtFast (row 28 51) 28 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 51) 28 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 51) 28 51 hvalid hfast

theorem sr28p52:∀ i ∈ List.range 1,StrictCheckAt 28 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 52) 28 52:=by decide +kernel
  have hfast:StrictAtFast (row 28 52) 28 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 52) 28 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 52) 28 52 hvalid hfast

theorem sr28p53:∀ i ∈ List.range 1,StrictCheckAt 28 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 53) 28 53:=by decide +kernel
  have hfast:StrictAtFast (row 28 53) 28 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 53) 28 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 53) 28 53 hvalid hfast

theorem sr28p54:∀ i ∈ List.range 1,StrictCheckAt 28 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 54) 28 54:=by decide +kernel
  have hfast:StrictAtFast (row 28 54) 28 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 54) 28 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 54) 28 54 hvalid hfast

theorem sr28p55:∀ i ∈ List.range 1,StrictCheckAt 28 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 55) 28 55:=by decide +kernel
  have hfast:StrictAtFast (row 28 55) 28 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 55) 28 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 55) 28 55 hvalid hfast

theorem sr28p56:∀ i ∈ List.range 1,StrictCheckAt 28 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 56) 28 56:=by decide +kernel
  have hfast:StrictAtFast (row 28 56) 28 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 56) 28 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 56) 28 56 hvalid hfast

theorem sr28p57:∀ i ∈ List.range 1,StrictCheckAt 28 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 57) 28 57:=by decide +kernel
  have hfast:StrictAtFast (row 28 57) 28 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 57) 28 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 57) 28 57 hvalid hfast

theorem sr28p58:∀ i ∈ List.range 1,StrictCheckAt 28 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 58) 28 58:=by decide +kernel
  have hfast:StrictAtFast (row 28 58) 28 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 58) 28 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 58) 28 58 hvalid hfast

theorem sr28p59:∀ i ∈ List.range 1,StrictCheckAt 28 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 59) 28 59:=by decide +kernel
  have hfast:StrictAtFast (row 28 59) 28 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 59) 28 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 59) 28 59 hvalid hfast

theorem sr28p60:∀ i ∈ List.range 1,StrictCheckAt 28 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 60) 28 60:=by decide +kernel
  have hfast:StrictAtFast (row 28 60) 28 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 60) 28 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 60) 28 60 hvalid hfast

theorem sr28p61:∀ i ∈ List.range 1,StrictCheckAt 28 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 61) 28 61:=by decide +kernel
  have hfast:StrictAtFast (row 28 61) 28 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 61) 28 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 61) 28 61 hvalid hfast

theorem sr28p62:∀ i ∈ List.range 1,StrictCheckAt 28 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 62) 28 62:=by decide +kernel
  have hfast:StrictAtFast (row 28 62) 28 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 62) 28 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 62) 28 62 hvalid hfast

theorem sr28p63:∀ i ∈ List.range 1,StrictCheckAt 28 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 63) 28 63:=by decide +kernel
  have hfast:StrictAtFast (row 28 63) 28 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 63) 28 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 63) 28 63 hvalid hfast

theorem sr28p64:∀ i ∈ List.range 1,StrictCheckAt 28 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 64) 28 64:=by decide +kernel
  have hfast:StrictAtFast (row 28 64) 28 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 64) 28 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 64) 28 64 hvalid hfast

theorem sr28p65:∀ i ∈ List.range 1,StrictCheckAt 28 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 65) 28 65:=by decide +kernel
  have hfast:StrictAtFast (row 28 65) 28 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 65) 28 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 65) 28 65 hvalid hfast

theorem sr28p66:∀ i ∈ List.range 1,StrictCheckAt 28 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 66) 28 66:=by decide +kernel
  have hfast:StrictAtFast (row 28 66) 28 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 66) 28 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 66) 28 66 hvalid hfast

theorem sr28p67:∀ i ∈ List.range 1,StrictCheckAt 28 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 67) 28 67:=by decide +kernel
  have hfast:StrictAtFast (row 28 67) 28 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 67) 28 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 67) 28 67 hvalid hfast

theorem sr28p68:∀ i ∈ List.range 1,StrictCheckAt 28 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 68) 28 68:=by decide +kernel
  have hfast:StrictAtFast (row 28 68) 28 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 68) 28 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 68) 28 68 hvalid hfast

theorem sr28p69:∀ i ∈ List.range 1,StrictCheckAt 28 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 69) 28 69:=by decide +kernel
  have hfast:StrictAtFast (row 28 69) 28 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 69) 28 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 69) 28 69 hvalid hfast

theorem sr28p70:∀ i ∈ List.range 1,StrictCheckAt 28 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 70) 28 70:=by decide +kernel
  have hfast:StrictAtFast (row 28 70) 28 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 70) 28 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 70) 28 70 hvalid hfast

theorem sr28p71:∀ i ∈ List.range 1,StrictCheckAt 28 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 71) 28 71:=by decide +kernel
  have hfast:StrictAtFast (row 28 71) 28 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 71) 28 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 71) 28 71 hvalid hfast

theorem sr28p72:∀ i ∈ List.range 1,StrictCheckAt 28 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 72) 28 72:=by decide +kernel
  have hfast:StrictAtFast (row 28 72) 28 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 72) 28 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 72) 28 72 hvalid hfast

theorem sr28p73:∀ i ∈ List.range 1,StrictCheckAt 28 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 73) 28 73:=by decide +kernel
  have hfast:StrictAtFast (row 28 73) 28 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 73) 28 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 73) 28 73 hvalid hfast

theorem sr28p74:∀ i ∈ List.range 1,StrictCheckAt 28 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 74) 28 74:=by decide +kernel
  have hfast:StrictAtFast (row 28 74) 28 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 74) 28 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 74) 28 74 hvalid hfast

theorem sr28p75:∀ i ∈ List.range 1,StrictCheckAt 28 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 75) 28 75:=by decide +kernel
  have hfast:StrictAtFast (row 28 75) 28 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 75) 28 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 75) 28 75 hvalid hfast

theorem sr28p76:∀ i ∈ List.range 1,StrictCheckAt 28 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 76) 28 76:=by decide +kernel
  have hfast:StrictAtFast (row 28 76) 28 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 76) 28 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 76) 28 76 hvalid hfast

theorem sr28p77:∀ i ∈ List.range 1,StrictCheckAt 28 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 77) 28 77:=by decide +kernel
  have hfast:StrictAtFast (row 28 77) 28 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 77) 28 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 77) 28 77 hvalid hfast

theorem sr28p78:∀ i ∈ List.range 1,StrictCheckAt 28 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 78) 28 78:=by decide +kernel
  have hfast:StrictAtFast (row 28 78) 28 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 78) 28 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 78) 28 78 hvalid hfast

theorem sr28p79:∀ i ∈ List.range 1,StrictCheckAt 28 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 79) 28 79:=by decide +kernel
  have hfast:StrictAtFast (row 28 79) 28 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 79) 28 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 79) 28 79 hvalid hfast

theorem sr28p80:∀ i ∈ List.range 1,StrictCheckAt 28 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 80) 28 80:=by decide +kernel
  have hfast:StrictAtFast (row 28 80) 28 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 80) 28 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 80) 28 80 hvalid hfast

theorem sr28p81:∀ i ∈ List.range 1,StrictCheckAt 28 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 81) 28 81:=by decide +kernel
  have hfast:StrictAtFast (row 28 81) 28 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 81) 28 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 81) 28 81 hvalid hfast

theorem sr28p82:∀ i ∈ List.range 1,StrictCheckAt 28 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 82) 28 82:=by decide +kernel
  have hfast:StrictAtFast (row 28 82) 28 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 82) 28 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 82) 28 82 hvalid hfast

theorem sr28p83:∀ i ∈ List.range 1,StrictCheckAt 28 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 83) 28 83:=by decide +kernel
  have hfast:StrictAtFast (row 28 83) 28 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 83) 28 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 83) 28 83 hvalid hfast

theorem sr28p84:∀ i ∈ List.range 1,StrictCheckAt 28 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 84) 28 84:=by decide +kernel
  have hfast:StrictAtFast (row 28 84) 28 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 84) 28 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 84) 28 84 hvalid hfast

theorem sr28p85:∀ i ∈ List.range 1,StrictCheckAt 28 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 85) 28 85:=by decide +kernel
  have hfast:StrictAtFast (row 28 85) 28 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 85) 28 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 85) 28 85 hvalid hfast

theorem sr28p86:∀ i ∈ List.range 1,StrictCheckAt 28 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 86) 28 86:=by decide +kernel
  have hfast:StrictAtFast (row 28 86) 28 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 86) 28 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 86) 28 86 hvalid hfast

theorem sr28p87:∀ i ∈ List.range 1,StrictCheckAt 28 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 87) 28 87:=by decide +kernel
  have hfast:StrictAtFast (row 28 87) 28 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 87) 28 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 87) 28 87 hvalid hfast

theorem sr28p88:∀ i ∈ List.range 1,StrictCheckAt 28 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 88) 28 88:=by decide +kernel
  have hfast:StrictAtFast (row 28 88) 28 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 88) 28 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 88) 28 88 hvalid hfast

theorem sr28p89:∀ i ∈ List.range 1,StrictCheckAt 28 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 89) 28 89:=by decide +kernel
  have hfast:StrictAtFast (row 28 89) 28 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 89) 28 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 89) 28 89 hvalid hfast

theorem sr28p90:∀ i ∈ List.range 1,StrictCheckAt 28 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 90) 28 90:=by decide +kernel
  have hfast:StrictAtFast (row 28 90) 28 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 90) 28 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 90) 28 90 hvalid hfast

theorem sr28p91:∀ i ∈ List.range 1,StrictCheckAt 28 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 91) 28 91:=by decide +kernel
  have hfast:StrictAtFast (row 28 91) 28 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 91) 28 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 91) 28 91 hvalid hfast

theorem sr28p92:∀ i ∈ List.range 1,StrictCheckAt 28 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 92) 28 92:=by decide +kernel
  have hfast:StrictAtFast (row 28 92) 28 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 92) 28 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 92) 28 92 hvalid hfast

theorem sr28p93:∀ i ∈ List.range 1,StrictCheckAt 28 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 93) 28 93:=by decide +kernel
  have hfast:StrictAtFast (row 28 93) 28 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 93) 28 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 93) 28 93 hvalid hfast

theorem sr28p94:∀ i ∈ List.range 1,StrictCheckAt 28 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 94) 28 94:=by decide +kernel
  have hfast:StrictAtFast (row 28 94) 28 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 94) 28 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 94) 28 94 hvalid hfast

theorem sr28p95:∀ i ∈ List.range 1,StrictCheckAt 28 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 95) 28 95:=by decide +kernel
  have hfast:StrictAtFast (row 28 95) 28 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 95) 28 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 95) 28 95 hvalid hfast

theorem sr28p96:∀ i ∈ List.range 1,StrictCheckAt 28 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 96) 28 96:=by decide +kernel
  have hfast:StrictAtFast (row 28 96) 28 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 96) 28 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 96) 28 96 hvalid hfast

theorem sr28p97:∀ i ∈ List.range 1,StrictCheckAt 28 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 97) 28 97:=by decide +kernel
  have hfast:StrictAtFast (row 28 97) 28 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 97) 28 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 97) 28 97 hvalid hfast

theorem sr28p98:∀ i ∈ List.range 1,StrictCheckAt 28 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 98) 28 98:=by decide +kernel
  have hfast:StrictAtFast (row 28 98) 28 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 98) 28 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 98) 28 98 hvalid hfast

theorem sr28p99:∀ i ∈ List.range 1,StrictCheckAt 28 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 99) 28 99:=by decide +kernel
  have hfast:StrictAtFast (row 28 99) 28 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 99) 28 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 99) 28 99 hvalid hfast

theorem sr28p100:∀ i ∈ List.range 1,StrictCheckAt 28 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 100) 28 100:=by decide +kernel
  have hfast:StrictAtFast (row 28 100) 28 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 100) 28 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 100) 28 100 hvalid hfast

theorem sr28p101:∀ i ∈ List.range 1,StrictCheckAt 28 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 101) 28 101:=by decide +kernel
  have hfast:StrictAtFast (row 28 101) 28 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 101) 28 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 101) 28 101 hvalid hfast

theorem sr28p102:∀ i ∈ List.range 1,StrictCheckAt 28 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 102) 28 102:=by decide +kernel
  have hfast:StrictAtFast (row 28 102) 28 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 102) 28 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 102) 28 102 hvalid hfast

theorem sr28p103:∀ i ∈ List.range 1,StrictCheckAt 28 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 103) 28 103:=by decide +kernel
  have hfast:StrictAtFast (row 28 103) 28 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 103) 28 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 103) 28 103 hvalid hfast

theorem sr28p104:∀ i ∈ List.range 1,StrictCheckAt 28 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 104) 28 104:=by decide +kernel
  have hfast:StrictAtFast (row 28 104) 28 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 104) 28 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 104) 28 104 hvalid hfast

theorem sr28p105:∀ i ∈ List.range 1,StrictCheckAt 28 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 105) 28 105:=by decide +kernel
  have hfast:StrictAtFast (row 28 105) 28 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 105) 28 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 105) 28 105 hvalid hfast

theorem sr28p106:∀ i ∈ List.range 1,StrictCheckAt 28 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 106) 28 106:=by decide +kernel
  have hfast:StrictAtFast (row 28 106) 28 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 106) 28 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 106) 28 106 hvalid hfast

theorem sr28p107:∀ i ∈ List.range 1,StrictCheckAt 28 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 107) 28 107:=by decide +kernel
  have hfast:StrictAtFast (row 28 107) 28 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 107) 28 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 107) 28 107 hvalid hfast

theorem sr28p108:∀ i ∈ List.range 1,StrictCheckAt 28 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 108) 28 108:=by decide +kernel
  have hfast:StrictAtFast (row 28 108) 28 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 108) 28 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 108) 28 108 hvalid hfast

theorem sr28p109:∀ i ∈ List.range 1,StrictCheckAt 28 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 109) 28 109:=by decide +kernel
  have hfast:StrictAtFast (row 28 109) 28 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 109) 28 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 109) 28 109 hvalid hfast

theorem sr28p110:∀ i ∈ List.range 1,StrictCheckAt 28 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 110) 28 110:=by decide +kernel
  have hfast:StrictAtFast (row 28 110) 28 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 110) 28 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 110) 28 110 hvalid hfast

theorem sr28p111:∀ i ∈ List.range 1,StrictCheckAt 28 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 111) 28 111:=by decide +kernel
  have hfast:StrictAtFast (row 28 111) 28 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 111) 28 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 111) 28 111 hvalid hfast

theorem sr28p112:∀ i ∈ List.range 1,StrictCheckAt 28 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 112) 28 112:=by decide +kernel
  have hfast:StrictAtFast (row 28 112) 28 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 112) 28 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 112) 28 112 hvalid hfast

theorem sr28p113:∀ i ∈ List.range 1,StrictCheckAt 28 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 113) 28 113:=by decide +kernel
  have hfast:StrictAtFast (row 28 113) 28 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 113) 28 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 113) 28 113 hvalid hfast

theorem sr28p114:∀ i ∈ List.range 1,StrictCheckAt 28 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 28 114) 28 114:=by decide +kernel
  have hfast:StrictAtFast (row 28 114) 28 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 28 114) 28 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 28 114) 28 114 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
