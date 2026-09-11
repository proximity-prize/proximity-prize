import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr21p0:∀ i ∈ List.range 8,CorrectAt 21 (0+i):=by decide +kernel

theorem cr21p1:∀ i ∈ List.range 8,CorrectAt 21 (8+i):=by decide +kernel

theorem cr21p2:∀ i ∈ List.range 8,CorrectAt 21 (16+i):=by decide +kernel

theorem cr21p3:∀ i ∈ List.range 8,CorrectAt 21 (24+i):=by decide +kernel

theorem cr21p4:∀ i ∈ List.range 8,CorrectAt 21 (32+i):=by decide +kernel

theorem cr21p5:∀ i ∈ List.range 8,CorrectAt 21 (40+i):=by decide +kernel

theorem cr21p6:∀ i ∈ List.range 8,CorrectAt 21 (48+i):=by decide +kernel

theorem cr21p7:∀ i ∈ List.range 8,CorrectAt 21 (56+i):=by decide +kernel

theorem cr21p8:∀ i ∈ List.range 8,CorrectAt 21 (64+i):=by decide +kernel

theorem cr21p9:∀ i ∈ List.range 8,CorrectAt 21 (72+i):=by decide +kernel

theorem cr21p10:∀ i ∈ List.range 8,CorrectAt 21 (80+i):=by decide +kernel

theorem cr21p11:∀ i ∈ List.range 8,CorrectAt 21 (88+i):=by decide +kernel

theorem cr21p12:∀ i ∈ List.range 8,CorrectAt 21 (96+i):=by decide +kernel

theorem cr21p13:∀ i ∈ List.range 8,CorrectAt 21 (104+i):=by decide +kernel

theorem cr21p14:∀ i ∈ List.range 8,CorrectAt 21 (112+i):=by decide +kernel

theorem cr21p15:∀ i ∈ List.range 2,CorrectAt 21 (120+i):=by decide +kernel

theorem sr21p0:∀ i ∈ List.range 1,StrictCheckAt 21 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 0) 21 0:=by decide +kernel
  have hfast:StrictAtFast (row 21 0) 21 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 0) 21 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 0) 21 0 hvalid hfast

theorem sr21p1:∀ i ∈ List.range 1,StrictCheckAt 21 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 1) 21 1:=by decide +kernel
  have hfast:StrictAtFast (row 21 1) 21 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 1) 21 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 1) 21 1 hvalid hfast

theorem sr21p2:∀ i ∈ List.range 1,StrictCheckAt 21 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 2) 21 2:=by decide +kernel
  have hfast:StrictAtFast (row 21 2) 21 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 2) 21 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 2) 21 2 hvalid hfast

theorem sr21p3:∀ i ∈ List.range 1,StrictCheckAt 21 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 3) 21 3:=by decide +kernel
  have hfast:StrictAtFast (row 21 3) 21 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 3) 21 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 3) 21 3 hvalid hfast

theorem sr21p4:∀ i ∈ List.range 1,StrictCheckAt 21 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 4) 21 4:=by decide +kernel
  have hfast:StrictAtFast (row 21 4) 21 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 4) 21 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 4) 21 4 hvalid hfast

theorem sr21p5:∀ i ∈ List.range 1,StrictCheckAt 21 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 5) 21 5:=by decide +kernel
  have hfast:StrictAtFast (row 21 5) 21 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 5) 21 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 5) 21 5 hvalid hfast

theorem sr21p6:∀ i ∈ List.range 1,StrictCheckAt 21 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 6) 21 6:=by decide +kernel
  have hfast:StrictAtFast (row 21 6) 21 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 6) 21 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 6) 21 6 hvalid hfast

theorem sr21p7:∀ i ∈ List.range 1,StrictCheckAt 21 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 7) 21 7:=by decide +kernel
  have hfast:StrictAtFast (row 21 7) 21 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 7) 21 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 7) 21 7 hvalid hfast

theorem sr21p8:∀ i ∈ List.range 1,StrictCheckAt 21 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 8) 21 8:=by decide +kernel
  have hfast:StrictAtFast (row 21 8) 21 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 8) 21 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 8) 21 8 hvalid hfast

theorem sr21p9:∀ i ∈ List.range 1,StrictCheckAt 21 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 9) 21 9:=by decide +kernel
  have hfast:StrictAtFast (row 21 9) 21 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 9) 21 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 9) 21 9 hvalid hfast

theorem sr21p10:∀ i ∈ List.range 1,StrictCheckAt 21 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 10) 21 10:=by decide +kernel
  have hfast:StrictAtFast (row 21 10) 21 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 10) 21 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 10) 21 10 hvalid hfast

theorem sr21p11:∀ i ∈ List.range 1,StrictCheckAt 21 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 11) 21 11:=by decide +kernel
  have hfast:StrictAtFast (row 21 11) 21 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 11) 21 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 11) 21 11 hvalid hfast

theorem sr21p12:∀ i ∈ List.range 1,StrictCheckAt 21 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 12) 21 12:=by decide +kernel
  have hfast:StrictAtFast (row 21 12) 21 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 12) 21 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 12) 21 12 hvalid hfast

theorem sr21p13:∀ i ∈ List.range 1,StrictCheckAt 21 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 13) 21 13:=by decide +kernel
  have hfast:StrictAtFast (row 21 13) 21 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 13) 21 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 13) 21 13 hvalid hfast

theorem sr21p14:∀ i ∈ List.range 1,StrictCheckAt 21 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 14) 21 14:=by decide +kernel
  have hfast:StrictAtFast (row 21 14) 21 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 14) 21 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 14) 21 14 hvalid hfast

theorem sr21p15:∀ i ∈ List.range 1,StrictCheckAt 21 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 15) 21 15:=by decide +kernel
  have hfast:StrictAtFast (row 21 15) 21 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 15) 21 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 15) 21 15 hvalid hfast

theorem sr21p16:∀ i ∈ List.range 1,StrictCheckAt 21 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 16) 21 16:=by decide +kernel
  have hfast:StrictAtFast (row 21 16) 21 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 16) 21 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 16) 21 16 hvalid hfast

theorem sr21p17:∀ i ∈ List.range 1,StrictCheckAt 21 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 17) 21 17:=by decide +kernel
  have hfast:StrictAtFast (row 21 17) 21 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 17) 21 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 17) 21 17 hvalid hfast

theorem sr21p18:∀ i ∈ List.range 1,StrictCheckAt 21 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 18) 21 18:=by decide +kernel
  have hfast:StrictAtFast (row 21 18) 21 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 18) 21 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 18) 21 18 hvalid hfast

theorem sr21p19:∀ i ∈ List.range 1,StrictCheckAt 21 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 19) 21 19:=by decide +kernel
  have hfast:StrictAtFast (row 21 19) 21 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 19) 21 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 19) 21 19 hvalid hfast

theorem sr21p20:∀ i ∈ List.range 1,StrictCheckAt 21 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 20) 21 20:=by decide +kernel
  have hfast:StrictAtFast (row 21 20) 21 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 20) 21 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 20) 21 20 hvalid hfast

theorem sr21p21:∀ i ∈ List.range 1,StrictCheckAt 21 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 21) 21 21:=by decide +kernel
  have hfast:StrictAtFast (row 21 21) 21 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 21) 21 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 21) 21 21 hvalid hfast

theorem sr21p22:∀ i ∈ List.range 1,StrictCheckAt 21 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 22) 21 22:=by decide +kernel
  have hfast:StrictAtFast (row 21 22) 21 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 22) 21 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 22) 21 22 hvalid hfast

theorem sr21p23:∀ i ∈ List.range 1,StrictCheckAt 21 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 23) 21 23:=by decide +kernel
  have hfast:StrictAtFast (row 21 23) 21 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 23) 21 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 23) 21 23 hvalid hfast

theorem sr21p24:∀ i ∈ List.range 1,StrictCheckAt 21 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 24) 21 24:=by decide +kernel
  have hfast:StrictAtFast (row 21 24) 21 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 24) 21 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 24) 21 24 hvalid hfast

theorem sr21p25:∀ i ∈ List.range 1,StrictCheckAt 21 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 25) 21 25:=by decide +kernel
  have hfast:StrictAtFast (row 21 25) 21 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 25) 21 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 25) 21 25 hvalid hfast

theorem sr21p26:∀ i ∈ List.range 1,StrictCheckAt 21 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 26) 21 26:=by decide +kernel
  have hfast:StrictAtFast (row 21 26) 21 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 26) 21 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 26) 21 26 hvalid hfast

theorem sr21p27:∀ i ∈ List.range 1,StrictCheckAt 21 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 27) 21 27:=by decide +kernel
  have hfast:StrictAtFast (row 21 27) 21 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 27) 21 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 27) 21 27 hvalid hfast

theorem sr21p28:∀ i ∈ List.range 1,StrictCheckAt 21 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 28) 21 28:=by decide +kernel
  have hfast:StrictAtFast (row 21 28) 21 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 28) 21 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 28) 21 28 hvalid hfast

theorem sr21p29:∀ i ∈ List.range 1,StrictCheckAt 21 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 29) 21 29:=by decide +kernel
  have hfast:StrictAtFast (row 21 29) 21 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 29) 21 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 29) 21 29 hvalid hfast

theorem sr21p30:∀ i ∈ List.range 1,StrictCheckAt 21 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 30) 21 30:=by decide +kernel
  have hfast:StrictAtFast (row 21 30) 21 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 30) 21 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 30) 21 30 hvalid hfast

theorem sr21p31:∀ i ∈ List.range 1,StrictCheckAt 21 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 31) 21 31:=by decide +kernel
  have hfast:StrictAtFast (row 21 31) 21 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 31) 21 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 31) 21 31 hvalid hfast

theorem sr21p32:∀ i ∈ List.range 1,StrictCheckAt 21 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 32) 21 32:=by decide +kernel
  have hfast:StrictAtFast (row 21 32) 21 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 32) 21 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 32) 21 32 hvalid hfast

theorem sr21p33:∀ i ∈ List.range 1,StrictCheckAt 21 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 33) 21 33:=by decide +kernel
  have hfast:StrictAtFast (row 21 33) 21 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 33) 21 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 33) 21 33 hvalid hfast

theorem sr21p34:∀ i ∈ List.range 1,StrictCheckAt 21 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 34) 21 34:=by decide +kernel
  have hfast:StrictAtFast (row 21 34) 21 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 34) 21 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 34) 21 34 hvalid hfast

theorem sr21p35:∀ i ∈ List.range 1,StrictCheckAt 21 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 35) 21 35:=by decide +kernel
  have hfast:StrictAtFast (row 21 35) 21 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 35) 21 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 35) 21 35 hvalid hfast

theorem sr21p36:∀ i ∈ List.range 1,StrictCheckAt 21 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 36) 21 36:=by decide +kernel
  have hfast:StrictAtFast (row 21 36) 21 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 36) 21 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 36) 21 36 hvalid hfast

theorem sr21p37:∀ i ∈ List.range 1,StrictCheckAt 21 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 37) 21 37:=by decide +kernel
  have hfast:StrictAtFast (row 21 37) 21 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 37) 21 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 37) 21 37 hvalid hfast

theorem sr21p38:∀ i ∈ List.range 1,StrictCheckAt 21 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 38) 21 38:=by decide +kernel
  have hfast:StrictAtFast (row 21 38) 21 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 38) 21 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 38) 21 38 hvalid hfast

theorem sr21p39:∀ i ∈ List.range 1,StrictCheckAt 21 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 39) 21 39:=by decide +kernel
  have hfast:StrictAtFast (row 21 39) 21 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 39) 21 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 39) 21 39 hvalid hfast

theorem sr21p40:∀ i ∈ List.range 1,StrictCheckAt 21 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 40) 21 40:=by decide +kernel
  have hfast:StrictAtFast (row 21 40) 21 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 40) 21 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 40) 21 40 hvalid hfast

theorem sr21p41:∀ i ∈ List.range 1,StrictCheckAt 21 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 41) 21 41:=by decide +kernel
  have hfast:StrictAtFast (row 21 41) 21 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 41) 21 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 41) 21 41 hvalid hfast

theorem sr21p42:∀ i ∈ List.range 1,StrictCheckAt 21 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 42) 21 42:=by decide +kernel
  have hfast:StrictAtFast (row 21 42) 21 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 42) 21 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 42) 21 42 hvalid hfast

theorem sr21p43:∀ i ∈ List.range 1,StrictCheckAt 21 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 43) 21 43:=by decide +kernel
  have hfast:StrictAtFast (row 21 43) 21 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 43) 21 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 43) 21 43 hvalid hfast

theorem sr21p44:∀ i ∈ List.range 1,StrictCheckAt 21 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 44) 21 44:=by decide +kernel
  have hfast:StrictAtFast (row 21 44) 21 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 44) 21 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 44) 21 44 hvalid hfast

theorem sr21p45:∀ i ∈ List.range 1,StrictCheckAt 21 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 45) 21 45:=by decide +kernel
  have hfast:StrictAtFast (row 21 45) 21 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 45) 21 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 45) 21 45 hvalid hfast

theorem sr21p46:∀ i ∈ List.range 1,StrictCheckAt 21 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 46) 21 46:=by decide +kernel
  have hfast:StrictAtFast (row 21 46) 21 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 46) 21 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 46) 21 46 hvalid hfast

theorem sr21p47:∀ i ∈ List.range 1,StrictCheckAt 21 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 47) 21 47:=by decide +kernel
  have hfast:StrictAtFast (row 21 47) 21 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 47) 21 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 47) 21 47 hvalid hfast

theorem sr21p48:∀ i ∈ List.range 1,StrictCheckAt 21 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 48) 21 48:=by decide +kernel
  have hfast:StrictAtFast (row 21 48) 21 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 48) 21 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 48) 21 48 hvalid hfast

theorem sr21p49:∀ i ∈ List.range 1,StrictCheckAt 21 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 49) 21 49:=by decide +kernel
  have hfast:StrictAtFast (row 21 49) 21 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 49) 21 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 49) 21 49 hvalid hfast

theorem sr21p50:∀ i ∈ List.range 1,StrictCheckAt 21 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 50) 21 50:=by decide +kernel
  have hfast:StrictAtFast (row 21 50) 21 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 50) 21 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 50) 21 50 hvalid hfast

theorem sr21p51:∀ i ∈ List.range 1,StrictCheckAt 21 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 51) 21 51:=by decide +kernel
  have hfast:StrictAtFast (row 21 51) 21 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 51) 21 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 51) 21 51 hvalid hfast

theorem sr21p52:∀ i ∈ List.range 1,StrictCheckAt 21 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 52) 21 52:=by decide +kernel
  have hfast:StrictAtFast (row 21 52) 21 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 52) 21 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 52) 21 52 hvalid hfast

theorem sr21p53:∀ i ∈ List.range 1,StrictCheckAt 21 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 53) 21 53:=by decide +kernel
  have hfast:StrictAtFast (row 21 53) 21 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 53) 21 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 53) 21 53 hvalid hfast

theorem sr21p54:∀ i ∈ List.range 1,StrictCheckAt 21 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 54) 21 54:=by decide +kernel
  have hfast:StrictAtFast (row 21 54) 21 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 54) 21 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 54) 21 54 hvalid hfast

theorem sr21p55:∀ i ∈ List.range 1,StrictCheckAt 21 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 55) 21 55:=by decide +kernel
  have hfast:StrictAtFast (row 21 55) 21 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 55) 21 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 55) 21 55 hvalid hfast

theorem sr21p56:∀ i ∈ List.range 1,StrictCheckAt 21 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 56) 21 56:=by decide +kernel
  have hfast:StrictAtFast (row 21 56) 21 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 56) 21 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 56) 21 56 hvalid hfast

theorem sr21p57:∀ i ∈ List.range 1,StrictCheckAt 21 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 57) 21 57:=by decide +kernel
  have hfast:StrictAtFast (row 21 57) 21 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 57) 21 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 57) 21 57 hvalid hfast

theorem sr21p58:∀ i ∈ List.range 1,StrictCheckAt 21 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 58) 21 58:=by decide +kernel
  have hfast:StrictAtFast (row 21 58) 21 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 58) 21 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 58) 21 58 hvalid hfast

theorem sr21p59:∀ i ∈ List.range 1,StrictCheckAt 21 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 59) 21 59:=by decide +kernel
  have hfast:StrictAtFast (row 21 59) 21 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 59) 21 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 59) 21 59 hvalid hfast

theorem sr21p60:∀ i ∈ List.range 1,StrictCheckAt 21 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 60) 21 60:=by decide +kernel
  have hfast:StrictAtFast (row 21 60) 21 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 60) 21 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 60) 21 60 hvalid hfast

theorem sr21p61:∀ i ∈ List.range 1,StrictCheckAt 21 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 61) 21 61:=by decide +kernel
  have hfast:StrictAtFast (row 21 61) 21 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 61) 21 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 61) 21 61 hvalid hfast

theorem sr21p62:∀ i ∈ List.range 1,StrictCheckAt 21 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 62) 21 62:=by decide +kernel
  have hfast:StrictAtFast (row 21 62) 21 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 62) 21 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 62) 21 62 hvalid hfast

theorem sr21p63:∀ i ∈ List.range 1,StrictCheckAt 21 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 63) 21 63:=by decide +kernel
  have hfast:StrictAtFast (row 21 63) 21 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 63) 21 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 63) 21 63 hvalid hfast

theorem sr21p64:∀ i ∈ List.range 1,StrictCheckAt 21 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 64) 21 64:=by decide +kernel
  have hfast:StrictAtFast (row 21 64) 21 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 64) 21 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 64) 21 64 hvalid hfast

theorem sr21p65:∀ i ∈ List.range 1,StrictCheckAt 21 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 65) 21 65:=by decide +kernel
  have hfast:StrictAtFast (row 21 65) 21 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 65) 21 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 65) 21 65 hvalid hfast

theorem sr21p66:∀ i ∈ List.range 1,StrictCheckAt 21 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 66) 21 66:=by decide +kernel
  have hfast:StrictAtFast (row 21 66) 21 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 66) 21 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 66) 21 66 hvalid hfast

theorem sr21p67:∀ i ∈ List.range 1,StrictCheckAt 21 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 67) 21 67:=by decide +kernel
  have hfast:StrictAtFast (row 21 67) 21 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 67) 21 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 67) 21 67 hvalid hfast

theorem sr21p68:∀ i ∈ List.range 1,StrictCheckAt 21 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 68) 21 68:=by decide +kernel
  have hfast:StrictAtFast (row 21 68) 21 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 68) 21 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 68) 21 68 hvalid hfast

theorem sr21p69:∀ i ∈ List.range 1,StrictCheckAt 21 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 69) 21 69:=by decide +kernel
  have hfast:StrictAtFast (row 21 69) 21 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 69) 21 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 69) 21 69 hvalid hfast

theorem sr21p70:∀ i ∈ List.range 1,StrictCheckAt 21 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 70) 21 70:=by decide +kernel
  have hfast:StrictAtFast (row 21 70) 21 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 70) 21 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 70) 21 70 hvalid hfast

theorem sr21p71:∀ i ∈ List.range 1,StrictCheckAt 21 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 71) 21 71:=by decide +kernel
  have hfast:StrictAtFast (row 21 71) 21 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 71) 21 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 71) 21 71 hvalid hfast

theorem sr21p72:∀ i ∈ List.range 1,StrictCheckAt 21 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 72) 21 72:=by decide +kernel
  have hfast:StrictAtFast (row 21 72) 21 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 72) 21 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 72) 21 72 hvalid hfast

theorem sr21p73:∀ i ∈ List.range 1,StrictCheckAt 21 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 73) 21 73:=by decide +kernel
  have hfast:StrictAtFast (row 21 73) 21 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 73) 21 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 73) 21 73 hvalid hfast

theorem sr21p74:∀ i ∈ List.range 1,StrictCheckAt 21 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 74) 21 74:=by decide +kernel
  have hfast:StrictAtFast (row 21 74) 21 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 74) 21 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 74) 21 74 hvalid hfast

theorem sr21p75:∀ i ∈ List.range 1,StrictCheckAt 21 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 75) 21 75:=by decide +kernel
  have hfast:StrictAtFast (row 21 75) 21 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 75) 21 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 75) 21 75 hvalid hfast

theorem sr21p76:∀ i ∈ List.range 1,StrictCheckAt 21 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 76) 21 76:=by decide +kernel
  have hfast:StrictAtFast (row 21 76) 21 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 76) 21 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 76) 21 76 hvalid hfast

theorem sr21p77:∀ i ∈ List.range 1,StrictCheckAt 21 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 77) 21 77:=by decide +kernel
  have hfast:StrictAtFast (row 21 77) 21 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 77) 21 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 77) 21 77 hvalid hfast

theorem sr21p78:∀ i ∈ List.range 1,StrictCheckAt 21 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 78) 21 78:=by decide +kernel
  have hfast:StrictAtFast (row 21 78) 21 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 78) 21 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 78) 21 78 hvalid hfast

theorem sr21p79:∀ i ∈ List.range 1,StrictCheckAt 21 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 79) 21 79:=by decide +kernel
  have hfast:StrictAtFast (row 21 79) 21 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 79) 21 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 79) 21 79 hvalid hfast

theorem sr21p80:∀ i ∈ List.range 1,StrictCheckAt 21 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 80) 21 80:=by decide +kernel
  have hfast:StrictAtFast (row 21 80) 21 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 80) 21 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 80) 21 80 hvalid hfast

theorem sr21p81:∀ i ∈ List.range 1,StrictCheckAt 21 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 81) 21 81:=by decide +kernel
  have hfast:StrictAtFast (row 21 81) 21 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 81) 21 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 81) 21 81 hvalid hfast

theorem sr21p82:∀ i ∈ List.range 1,StrictCheckAt 21 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 82) 21 82:=by decide +kernel
  have hfast:StrictAtFast (row 21 82) 21 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 82) 21 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 82) 21 82 hvalid hfast

theorem sr21p83:∀ i ∈ List.range 1,StrictCheckAt 21 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 83) 21 83:=by decide +kernel
  have hfast:StrictAtFast (row 21 83) 21 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 83) 21 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 83) 21 83 hvalid hfast

theorem sr21p84:∀ i ∈ List.range 1,StrictCheckAt 21 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 84) 21 84:=by decide +kernel
  have hfast:StrictAtFast (row 21 84) 21 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 84) 21 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 84) 21 84 hvalid hfast

theorem sr21p85:∀ i ∈ List.range 1,StrictCheckAt 21 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 85) 21 85:=by decide +kernel
  have hfast:StrictAtFast (row 21 85) 21 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 85) 21 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 85) 21 85 hvalid hfast

theorem sr21p86:∀ i ∈ List.range 1,StrictCheckAt 21 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 86) 21 86:=by decide +kernel
  have hfast:StrictAtFast (row 21 86) 21 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 86) 21 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 86) 21 86 hvalid hfast

theorem sr21p87:∀ i ∈ List.range 1,StrictCheckAt 21 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 87) 21 87:=by decide +kernel
  have hfast:StrictAtFast (row 21 87) 21 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 87) 21 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 87) 21 87 hvalid hfast

theorem sr21p88:∀ i ∈ List.range 1,StrictCheckAt 21 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 88) 21 88:=by decide +kernel
  have hfast:StrictAtFast (row 21 88) 21 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 88) 21 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 88) 21 88 hvalid hfast

theorem sr21p89:∀ i ∈ List.range 1,StrictCheckAt 21 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 89) 21 89:=by decide +kernel
  have hfast:StrictAtFast (row 21 89) 21 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 89) 21 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 89) 21 89 hvalid hfast

theorem sr21p90:∀ i ∈ List.range 1,StrictCheckAt 21 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 90) 21 90:=by decide +kernel
  have hfast:StrictAtFast (row 21 90) 21 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 90) 21 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 90) 21 90 hvalid hfast

theorem sr21p91:∀ i ∈ List.range 1,StrictCheckAt 21 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 91) 21 91:=by decide +kernel
  have hfast:StrictAtFast (row 21 91) 21 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 91) 21 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 91) 21 91 hvalid hfast

theorem sr21p92:∀ i ∈ List.range 1,StrictCheckAt 21 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 92) 21 92:=by decide +kernel
  have hfast:StrictAtFast (row 21 92) 21 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 92) 21 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 92) 21 92 hvalid hfast

theorem sr21p93:∀ i ∈ List.range 1,StrictCheckAt 21 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 93) 21 93:=by decide +kernel
  have hfast:StrictAtFast (row 21 93) 21 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 93) 21 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 93) 21 93 hvalid hfast

theorem sr21p94:∀ i ∈ List.range 1,StrictCheckAt 21 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 94) 21 94:=by decide +kernel
  have hfast:StrictAtFast (row 21 94) 21 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 94) 21 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 94) 21 94 hvalid hfast

theorem sr21p95:∀ i ∈ List.range 1,StrictCheckAt 21 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 95) 21 95:=by decide +kernel
  have hfast:StrictAtFast (row 21 95) 21 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 95) 21 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 95) 21 95 hvalid hfast

theorem sr21p96:∀ i ∈ List.range 1,StrictCheckAt 21 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 96) 21 96:=by decide +kernel
  have hfast:StrictAtFast (row 21 96) 21 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 96) 21 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 96) 21 96 hvalid hfast

theorem sr21p97:∀ i ∈ List.range 1,StrictCheckAt 21 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 97) 21 97:=by decide +kernel
  have hfast:StrictAtFast (row 21 97) 21 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 97) 21 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 97) 21 97 hvalid hfast

theorem sr21p98:∀ i ∈ List.range 1,StrictCheckAt 21 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 98) 21 98:=by decide +kernel
  have hfast:StrictAtFast (row 21 98) 21 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 98) 21 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 98) 21 98 hvalid hfast

theorem sr21p99:∀ i ∈ List.range 1,StrictCheckAt 21 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 99) 21 99:=by decide +kernel
  have hfast:StrictAtFast (row 21 99) 21 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 99) 21 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 99) 21 99 hvalid hfast

theorem sr21p100:∀ i ∈ List.range 1,StrictCheckAt 21 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 100) 21 100:=by decide +kernel
  have hfast:StrictAtFast (row 21 100) 21 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 100) 21 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 100) 21 100 hvalid hfast

theorem sr21p101:∀ i ∈ List.range 1,StrictCheckAt 21 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 101) 21 101:=by decide +kernel
  have hfast:StrictAtFast (row 21 101) 21 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 101) 21 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 101) 21 101 hvalid hfast

theorem sr21p102:∀ i ∈ List.range 1,StrictCheckAt 21 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 102) 21 102:=by decide +kernel
  have hfast:StrictAtFast (row 21 102) 21 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 102) 21 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 102) 21 102 hvalid hfast

theorem sr21p103:∀ i ∈ List.range 1,StrictCheckAt 21 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 103) 21 103:=by decide +kernel
  have hfast:StrictAtFast (row 21 103) 21 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 103) 21 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 103) 21 103 hvalid hfast

theorem sr21p104:∀ i ∈ List.range 1,StrictCheckAt 21 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 104) 21 104:=by decide +kernel
  have hfast:StrictAtFast (row 21 104) 21 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 104) 21 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 104) 21 104 hvalid hfast

theorem sr21p105:∀ i ∈ List.range 1,StrictCheckAt 21 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 105) 21 105:=by decide +kernel
  have hfast:StrictAtFast (row 21 105) 21 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 105) 21 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 105) 21 105 hvalid hfast

theorem sr21p106:∀ i ∈ List.range 1,StrictCheckAt 21 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 106) 21 106:=by decide +kernel
  have hfast:StrictAtFast (row 21 106) 21 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 106) 21 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 106) 21 106 hvalid hfast

theorem sr21p107:∀ i ∈ List.range 1,StrictCheckAt 21 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 107) 21 107:=by decide +kernel
  have hfast:StrictAtFast (row 21 107) 21 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 107) 21 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 107) 21 107 hvalid hfast

theorem sr21p108:∀ i ∈ List.range 1,StrictCheckAt 21 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 108) 21 108:=by decide +kernel
  have hfast:StrictAtFast (row 21 108) 21 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 108) 21 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 108) 21 108 hvalid hfast

theorem sr21p109:∀ i ∈ List.range 1,StrictCheckAt 21 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 109) 21 109:=by decide +kernel
  have hfast:StrictAtFast (row 21 109) 21 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 109) 21 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 109) 21 109 hvalid hfast

theorem sr21p110:∀ i ∈ List.range 1,StrictCheckAt 21 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 110) 21 110:=by decide +kernel
  have hfast:StrictAtFast (row 21 110) 21 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 110) 21 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 110) 21 110 hvalid hfast

theorem sr21p111:∀ i ∈ List.range 1,StrictCheckAt 21 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 111) 21 111:=by decide +kernel
  have hfast:StrictAtFast (row 21 111) 21 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 111) 21 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 111) 21 111 hvalid hfast

theorem sr21p112:∀ i ∈ List.range 1,StrictCheckAt 21 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 112) 21 112:=by decide +kernel
  have hfast:StrictAtFast (row 21 112) 21 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 112) 21 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 112) 21 112 hvalid hfast

theorem sr21p113:∀ i ∈ List.range 1,StrictCheckAt 21 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 113) 21 113:=by decide +kernel
  have hfast:StrictAtFast (row 21 113) 21 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 113) 21 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 113) 21 113 hvalid hfast

theorem sr21p114:∀ i ∈ List.range 1,StrictCheckAt 21 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 114) 21 114:=by decide +kernel
  have hfast:StrictAtFast (row 21 114) 21 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 114) 21 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 114) 21 114 hvalid hfast

theorem sr21p115:∀ i ∈ List.range 1,StrictCheckAt 21 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 115) 21 115:=by decide +kernel
  have hfast:StrictAtFast (row 21 115) 21 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 115) 21 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 115) 21 115 hvalid hfast

theorem sr21p116:∀ i ∈ List.range 1,StrictCheckAt 21 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 116) 21 116:=by decide +kernel
  have hfast:StrictAtFast (row 21 116) 21 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 116) 21 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 116) 21 116 hvalid hfast

theorem sr21p117:∀ i ∈ List.range 1,StrictCheckAt 21 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 117) 21 117:=by decide +kernel
  have hfast:StrictAtFast (row 21 117) 21 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 117) 21 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 117) 21 117 hvalid hfast

theorem sr21p118:∀ i ∈ List.range 1,StrictCheckAt 21 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 118) 21 118:=by decide +kernel
  have hfast:StrictAtFast (row 21 118) 21 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 118) 21 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 118) 21 118 hvalid hfast

theorem sr21p119:∀ i ∈ List.range 1,StrictCheckAt 21 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 119) 21 119:=by decide +kernel
  have hfast:StrictAtFast (row 21 119) 21 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 119) 21 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 119) 21 119 hvalid hfast

theorem sr21p120:∀ i ∈ List.range 1,StrictCheckAt 21 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 120) 21 120:=by decide +kernel
  have hfast:StrictAtFast (row 21 120) 21 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 120) 21 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 120) 21 120 hvalid hfast

theorem sr21p121:∀ i ∈ List.range 1,StrictCheckAt 21 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 21 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 21 121) 21 121:=by decide +kernel
  have hfast:StrictAtFast (row 21 121) 21 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 21 121) 21 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 21 121) 21 121 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
