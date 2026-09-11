import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

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

theorem br26p0:∀ i ∈ List.range 4,BaseCheckAt 26 (0+i):=by decide +kernel

theorem br26p1:∀ i ∈ List.range 4,BaseCheckAt 26 (4+i):=by decide +kernel

theorem br26p2:∀ i ∈ List.range 4,BaseCheckAt 26 (8+i):=by decide +kernel

theorem br26p3:∀ i ∈ List.range 4,BaseCheckAt 26 (12+i):=by decide +kernel

theorem br26p4:∀ i ∈ List.range 4,BaseCheckAt 26 (16+i):=by decide +kernel

theorem br26p5:∀ i ∈ List.range 4,BaseCheckAt 26 (20+i):=by decide +kernel

theorem br26p6:∀ i ∈ List.range 4,BaseCheckAt 26 (24+i):=by decide +kernel

theorem br26p7:∀ i ∈ List.range 4,BaseCheckAt 26 (28+i):=by decide +kernel

theorem br26p8:∀ i ∈ List.range 4,BaseCheckAt 26 (32+i):=by decide +kernel

theorem br26p9:∀ i ∈ List.range 4,BaseCheckAt 26 (36+i):=by decide +kernel

theorem br26p10:∀ i ∈ List.range 4,BaseCheckAt 26 (40+i):=by decide +kernel

theorem br26p11:∀ i ∈ List.range 4,BaseCheckAt 26 (44+i):=by decide +kernel

theorem br26p12:∀ i ∈ List.range 4,BaseCheckAt 26 (48+i):=by decide +kernel

theorem br26p13:∀ i ∈ List.range 4,BaseCheckAt 26 (52+i):=by decide +kernel

theorem br26p14:∀ i ∈ List.range 4,BaseCheckAt 26 (56+i):=by decide +kernel

theorem br26p15:∀ i ∈ List.range 4,BaseCheckAt 26 (60+i):=by decide +kernel



theorem br26p16:∀ i ∈ List.range 4,BaseCheckAt 26 (64+i):=by decide +kernel

theorem br26p17:∀ i ∈ List.range 4,BaseCheckAt 26 (68+i):=by decide +kernel

theorem br26p18:∀ i ∈ List.range 4,BaseCheckAt 26 (72+i):=by decide +kernel

theorem br26p19:∀ i ∈ List.range 4,BaseCheckAt 26 (76+i):=by decide +kernel

theorem br26p20:∀ i ∈ List.range 4,BaseCheckAt 26 (80+i):=by decide +kernel

theorem br26p21:∀ i ∈ List.range 4,BaseCheckAt 26 (84+i):=by decide +kernel

theorem br26p22:∀ i ∈ List.range 4,BaseCheckAt 26 (88+i):=by decide +kernel

theorem br26p23:∀ i ∈ List.range 4,BaseCheckAt 26 (92+i):=by decide +kernel

theorem br26p24:∀ i ∈ List.range 4,BaseCheckAt 26 (96+i):=by decide +kernel

theorem br26p25:∀ i ∈ List.range 4,BaseCheckAt 26 (100+i):=by decide +kernel

theorem br26p26:∀ i ∈ List.range 4,BaseCheckAt 26 (104+i):=by decide +kernel

theorem br26p27:∀ i ∈ List.range 4,BaseCheckAt 26 (108+i):=by decide +kernel

theorem br26p28:∀ i ∈ List.range 4,BaseCheckAt 26 (112+i):=by decide +kernel

theorem br26p29:∀ i ∈ List.range 1,BaseCheckAt 26 (116+i):=by decide +kernel



theorem cr26:∀ V ∈ List.range 117,CorrectAt 26 V:=by
  intro V hV
  have hv:V < 117:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr26p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr26p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr26p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr26p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr26p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr26p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr26p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr26p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr26p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr26p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr26p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr26p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr26p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr26p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr26p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr26:∀ V ∈ List.range 117,ZeroCheckAt 26 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 26 V (by omega) (by omega) (by omega)
theorem sr26:∀ V ∈ List.range 117,StrictCheckAt 26 V:=by
  intro V hV
  have hv:V < 117:=List.mem_range.mp hV
  by_cases h0_117:V < 58
  · by_cases h0_58:V < 29
    · by_cases h0_29:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr26p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr26p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr26p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr26p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr26p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr26p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr26p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr26p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr26p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr26p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr26p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr26p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr26p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr26p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_29:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr26p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr26p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr26p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr26p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr26p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr26p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr26p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_29:V < 25
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have h:=sr26p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr26p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
            · by_cases h23_25:V < 24
              · have h:=sr26p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr26p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have h:=sr26p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr26p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
            · by_cases h27_29:V < 28
              · have h:=sr26p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr26p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h29_58:V < 43
      · by_cases h29_43:V < 36
        · by_cases h29_36:V < 32
          · by_cases h29_32:V < 30
            · have h:=sr26p29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_32:V < 31
              · have h:=sr26p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · have h:=sr26p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have h:=sr26p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr26p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
            · by_cases h34_36:V < 35
              · have h:=sr26p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr26p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
        · by_cases h36_43:V < 39
          · by_cases h36_39:V < 37
            · have h:=sr26p36 (V-36) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
            · by_cases h37_39:V < 38
              · have h:=sr26p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr26p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have h:=sr26p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr26p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
            · by_cases h41_43:V < 42
              · have h:=sr26p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr26p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
      · by_cases h43_58:V < 50
        · by_cases h43_50:V < 46
          · by_cases h43_46:V < 44
            · have h:=sr26p43 (V-43) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
            · by_cases h44_46:V < 45
              · have h:=sr26p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr26p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
          · by_cases h46_50:V < 48
            · by_cases h46_48:V < 47
              · have h:=sr26p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr26p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
            · by_cases h48_50:V < 49
              · have h:=sr26p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr26p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
        · by_cases h50_58:V < 54
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have h:=sr26p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr26p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
            · by_cases h52_54:V < 53
              · have h:=sr26p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr26p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have h:=sr26p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr26p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
            · by_cases h56_58:V < 57
              · have h:=sr26p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr26p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
  · by_cases h58_117:V < 87
    · by_cases h58_87:V < 72
      · by_cases h58_72:V < 65
        · by_cases h58_65:V < 61
          · by_cases h58_61:V < 59
            · have h:=sr26p58 (V-58) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
            · by_cases h59_61:V < 60
              · have h:=sr26p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr26p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · by_cases h61_65:V < 63
            · by_cases h61_63:V < 62
              · have h:=sr26p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr26p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
            · by_cases h63_65:V < 64
              · have h:=sr26p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr26p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · by_cases h65_72:V < 68
          · by_cases h65_68:V < 66
            · have h:=sr26p65 (V-65) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
            · by_cases h66_68:V < 67
              · have h:=sr26p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr26p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have h:=sr26p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr26p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
            · by_cases h70_72:V < 71
              · have h:=sr26p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr26p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
      · by_cases h72_87:V < 79
        · by_cases h72_79:V < 75
          · by_cases h72_75:V < 73
            · have h:=sr26p72 (V-72) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
            · by_cases h73_75:V < 74
              · have h:=sr26p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr26p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have h:=sr26p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr26p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
            · by_cases h77_79:V < 78
              · have h:=sr26p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr26p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
        · by_cases h79_87:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have h:=sr26p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr26p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
            · by_cases h81_83:V < 82
              · have h:=sr26p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr26p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have h:=sr26p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr26p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
            · by_cases h85_87:V < 86
              · have h:=sr26p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr26p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
    · by_cases h87_117:V < 102
      · by_cases h87_102:V < 94
        · by_cases h87_94:V < 90
          · by_cases h87_90:V < 88
            · have h:=sr26p87 (V-87) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
            · by_cases h88_90:V < 89
              · have h:=sr26p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr26p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have h:=sr26p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr26p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr26p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr26p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
        · by_cases h94_102:V < 98
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have h:=sr26p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr26p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
            · by_cases h96_98:V < 97
              · have h:=sr26p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr26p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
          · by_cases h98_102:V < 100
            · by_cases h98_100:V < 99
              · have h:=sr26p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr26p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
            · by_cases h100_102:V < 101
              · have h:=sr26p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr26p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
      · by_cases h102_117:V < 109
        · by_cases h102_109:V < 105
          · by_cases h102_105:V < 103
            · have h:=sr26p102 (V-102) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr26p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr26p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have h:=sr26p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr26p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
            · by_cases h107_109:V < 108
              · have h:=sr26p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr26p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
        · by_cases h109_117:V < 113
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have h:=sr26p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr26p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
            · by_cases h111_113:V < 112
              · have h:=sr26p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr26p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · by_cases h113_117:V < 115
            · by_cases h113_115:V < 114
              · have h:=sr26p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr26p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
            · by_cases h115_117:V < 116
              · have h:=sr26p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr26p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h

theorem br26:∀ V ∈ List.range 117,BaseCheckAt 26 V:=by
  intro V hV
  have hv:V < 117:=List.mem_range.mp hV
  by_cases h0_30:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br26p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br26p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br26p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br26p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br26p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br26p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br26p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br26p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br26p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br26p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br26p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br26p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br26p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br26p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br26p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_30:V < 88
    · by_cases h15_22:V < 72
      · by_cases h15_18:V < 64
        · have h:=br26p15 (V-60) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
        · by_cases h16_18:V < 68
          · have h:=br26p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br26p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
      · by_cases h18_22:V < 80
        · by_cases h18_20:V < 76
          · have h:=br26p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br26p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
        · by_cases h20_22:V < 84
          · have h:=br26p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br26p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
    · by_cases h22_30:V < 104
      · by_cases h22_26:V < 96
        · by_cases h22_24:V < 92
          · have h:=br26p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br26p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
        · by_cases h24_26:V < 100
          · have h:=br26p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br26p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
      · by_cases h26_30:V < 112
        · by_cases h26_28:V < 108
          · have h:=br26p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br26p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
        · by_cases h28_30:V < 116
          · have h:=br26p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br26p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
