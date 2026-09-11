import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

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

theorem br23p0:∀ i ∈ List.range 4,BaseCheckAt 23 (0+i):=by decide +kernel

theorem br23p1:∀ i ∈ List.range 4,BaseCheckAt 23 (4+i):=by decide +kernel

theorem br23p2:∀ i ∈ List.range 4,BaseCheckAt 23 (8+i):=by decide +kernel

theorem br23p3:∀ i ∈ List.range 4,BaseCheckAt 23 (12+i):=by decide +kernel

theorem br23p4:∀ i ∈ List.range 4,BaseCheckAt 23 (16+i):=by decide +kernel

theorem br23p5:∀ i ∈ List.range 4,BaseCheckAt 23 (20+i):=by decide +kernel

theorem br23p6:∀ i ∈ List.range 4,BaseCheckAt 23 (24+i):=by decide +kernel

theorem br23p7:∀ i ∈ List.range 4,BaseCheckAt 23 (28+i):=by decide +kernel

theorem br23p8:∀ i ∈ List.range 4,BaseCheckAt 23 (32+i):=by decide +kernel

theorem br23p9:∀ i ∈ List.range 4,BaseCheckAt 23 (36+i):=by decide +kernel

theorem br23p10:∀ i ∈ List.range 4,BaseCheckAt 23 (40+i):=by decide +kernel

theorem br23p11:∀ i ∈ List.range 4,BaseCheckAt 23 (44+i):=by decide +kernel

theorem br23p12:∀ i ∈ List.range 4,BaseCheckAt 23 (48+i):=by decide +kernel

theorem br23p13:∀ i ∈ List.range 4,BaseCheckAt 23 (52+i):=by decide +kernel

theorem br23p14:∀ i ∈ List.range 4,BaseCheckAt 23 (56+i):=by decide +kernel

theorem br23p15:∀ i ∈ List.range 4,BaseCheckAt 23 (60+i):=by decide +kernel



theorem br23p16:∀ i ∈ List.range 4,BaseCheckAt 23 (64+i):=by decide +kernel

theorem br23p17:∀ i ∈ List.range 4,BaseCheckAt 23 (68+i):=by decide +kernel

theorem br23p18:∀ i ∈ List.range 4,BaseCheckAt 23 (72+i):=by decide +kernel

theorem br23p19:∀ i ∈ List.range 4,BaseCheckAt 23 (76+i):=by decide +kernel

theorem br23p20:∀ i ∈ List.range 4,BaseCheckAt 23 (80+i):=by decide +kernel

theorem br23p21:∀ i ∈ List.range 4,BaseCheckAt 23 (84+i):=by decide +kernel

theorem br23p22:∀ i ∈ List.range 4,BaseCheckAt 23 (88+i):=by decide +kernel

theorem br23p23:∀ i ∈ List.range 4,BaseCheckAt 23 (92+i):=by decide +kernel

theorem br23p24:∀ i ∈ List.range 4,BaseCheckAt 23 (96+i):=by decide +kernel

theorem br23p25:∀ i ∈ List.range 4,BaseCheckAt 23 (100+i):=by decide +kernel

theorem br23p26:∀ i ∈ List.range 4,BaseCheckAt 23 (104+i):=by decide +kernel

theorem br23p27:∀ i ∈ List.range 4,BaseCheckAt 23 (108+i):=by decide +kernel

theorem br23p28:∀ i ∈ List.range 4,BaseCheckAt 23 (112+i):=by decide +kernel

theorem br23p29:∀ i ∈ List.range 4,BaseCheckAt 23 (116+i):=by decide +kernel



theorem cr23:∀ V ∈ List.range 120,CorrectAt 23 V:=by
  intro V hV
  have hv:V < 120:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr23p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr23p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr23p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr23p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr23p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr23p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr23p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr23p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr23p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr23p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr23p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr23p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr23p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr23p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr23p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr23:∀ V ∈ List.range 120,ZeroCheckAt 23 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 23 V (by omega) (by omega) (by omega)
theorem sr23:∀ V ∈ List.range 120,StrictCheckAt 23 V:=by
  intro V hV
  have hv:V < 120:=List.mem_range.mp hV
  by_cases h0_120:V < 60
  · by_cases h0_60:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr23p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr23p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr23p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr23p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr23p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr23p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr23p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr23p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr23p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr23p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr23p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr23p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr23p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr23p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr23p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have h:=sr23p15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
            · by_cases h16_18:V < 17
              · have h:=sr23p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr23p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have h:=sr23p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr23p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
            · by_cases h20_22:V < 21
              · have h:=sr23p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr23p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have h:=sr23p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr23p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
            · by_cases h24_26:V < 25
              · have h:=sr23p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr23p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have h:=sr23p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr23p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
            · by_cases h28_30:V < 29
              · have h:=sr23p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr23p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
    · by_cases h30_60:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have h:=sr23p30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
            · by_cases h31_33:V < 32
              · have h:=sr23p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr23p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have h:=sr23p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr23p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
            · by_cases h35_37:V < 36
              · have h:=sr23p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr23p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have h:=sr23p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr23p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
            · by_cases h39_41:V < 40
              · have h:=sr23p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr23p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have h:=sr23p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr23p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr23p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr23p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h45_60:V < 52
        · by_cases h45_52:V < 48
          · by_cases h45_48:V < 46
            · have h:=sr23p45 (V-45) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
            · by_cases h46_48:V < 47
              · have h:=sr23p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr23p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
          · by_cases h48_52:V < 50
            · by_cases h48_50:V < 49
              · have h:=sr23p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr23p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
            · by_cases h50_52:V < 51
              · have h:=sr23p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr23p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
        · by_cases h52_60:V < 56
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have h:=sr23p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr23p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
            · by_cases h54_56:V < 55
              · have h:=sr23p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr23p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
          · by_cases h56_60:V < 58
            · by_cases h56_58:V < 57
              · have h:=sr23p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr23p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
            · by_cases h58_60:V < 59
              · have h:=sr23p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr23p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
  · by_cases h60_120:V < 90
    · by_cases h60_90:V < 75
      · by_cases h60_75:V < 67
        · by_cases h60_67:V < 63
          · by_cases h60_63:V < 61
            · have h:=sr23p60 (V-60) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · by_cases h61_63:V < 62
              · have h:=sr23p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr23p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
          · by_cases h63_67:V < 65
            · by_cases h63_65:V < 64
              · have h:=sr23p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr23p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
            · by_cases h65_67:V < 66
              · have h:=sr23p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr23p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
        · by_cases h67_75:V < 71
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have h:=sr23p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr23p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
            · by_cases h69_71:V < 70
              · have h:=sr23p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr23p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have h:=sr23p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr23p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
            · by_cases h73_75:V < 74
              · have h:=sr23p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr23p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
      · by_cases h75_90:V < 82
        · by_cases h75_82:V < 78
          · by_cases h75_78:V < 76
            · have h:=sr23p75 (V-75) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
            · by_cases h76_78:V < 77
              · have h:=sr23p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr23p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have h:=sr23p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr23p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
            · by_cases h80_82:V < 81
              · have h:=sr23p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr23p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have h:=sr23p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr23p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
            · by_cases h84_86:V < 85
              · have h:=sr23p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr23p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have h:=sr23p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr23p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
            · by_cases h88_90:V < 89
              · have h:=sr23p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr23p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
    · by_cases h90_120:V < 105
      · by_cases h90_105:V < 97
        · by_cases h90_97:V < 93
          · by_cases h90_93:V < 91
            · have h:=sr23p90 (V-90) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr23p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr23p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · by_cases h93_97:V < 95
            · by_cases h93_95:V < 94
              · have h:=sr23p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr23p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
            · by_cases h95_97:V < 96
              · have h:=sr23p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr23p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · by_cases h97_105:V < 101
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have h:=sr23p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr23p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_101:V < 100
              · have h:=sr23p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr23p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have h:=sr23p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr23p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr23p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr23p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h105_120:V < 112
        · by_cases h105_112:V < 108
          · by_cases h105_108:V < 106
            · have h:=sr23p105 (V-105) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
            · by_cases h106_108:V < 107
              · have h:=sr23p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr23p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have h:=sr23p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr23p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
            · by_cases h110_112:V < 111
              · have h:=sr23p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr23p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
        · by_cases h112_120:V < 116
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have h:=sr23p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr23p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
            · by_cases h114_116:V < 115
              · have h:=sr23p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr23p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
          · by_cases h116_120:V < 118
            · by_cases h116_118:V < 117
              · have h:=sr23p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr23p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
            · by_cases h118_120:V < 119
              · have h:=sr23p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr23p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h

theorem br23:∀ V ∈ List.range 120,BaseCheckAt 23 V:=by
  intro V hV
  have hv:V < 120:=List.mem_range.mp hV
  by_cases h0_30:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br23p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br23p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br23p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br23p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br23p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br23p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br23p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br23p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br23p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br23p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br23p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br23p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br23p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br23p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br23p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_30:V < 88
    · by_cases h15_22:V < 72
      · by_cases h15_18:V < 64
        · have h:=br23p15 (V-60) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
        · by_cases h16_18:V < 68
          · have h:=br23p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br23p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
      · by_cases h18_22:V < 80
        · by_cases h18_20:V < 76
          · have h:=br23p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br23p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
        · by_cases h20_22:V < 84
          · have h:=br23p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br23p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
    · by_cases h22_30:V < 104
      · by_cases h22_26:V < 96
        · by_cases h22_24:V < 92
          · have h:=br23p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br23p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
        · by_cases h24_26:V < 100
          · have h:=br23p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br23p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
      · by_cases h26_30:V < 112
        · by_cases h26_28:V < 108
          · have h:=br23p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br23p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
        · by_cases h28_30:V < 116
          · have h:=br23p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br23p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
