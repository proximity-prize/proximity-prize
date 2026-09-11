import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

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

theorem br28p0:∀ i ∈ List.range 4,BaseCheckAt 28 (0+i):=by decide +kernel

theorem br28p1:∀ i ∈ List.range 4,BaseCheckAt 28 (4+i):=by decide +kernel

theorem br28p2:∀ i ∈ List.range 4,BaseCheckAt 28 (8+i):=by decide +kernel

theorem br28p3:∀ i ∈ List.range 4,BaseCheckAt 28 (12+i):=by decide +kernel

theorem br28p4:∀ i ∈ List.range 4,BaseCheckAt 28 (16+i):=by decide +kernel

theorem br28p5:∀ i ∈ List.range 4,BaseCheckAt 28 (20+i):=by decide +kernel

theorem br28p6:∀ i ∈ List.range 4,BaseCheckAt 28 (24+i):=by decide +kernel

theorem br28p7:∀ i ∈ List.range 4,BaseCheckAt 28 (28+i):=by decide +kernel

theorem br28p8:∀ i ∈ List.range 4,BaseCheckAt 28 (32+i):=by decide +kernel

theorem br28p9:∀ i ∈ List.range 4,BaseCheckAt 28 (36+i):=by decide +kernel

theorem br28p10:∀ i ∈ List.range 4,BaseCheckAt 28 (40+i):=by decide +kernel

theorem br28p11:∀ i ∈ List.range 4,BaseCheckAt 28 (44+i):=by decide +kernel

theorem br28p12:∀ i ∈ List.range 4,BaseCheckAt 28 (48+i):=by decide +kernel

theorem br28p13:∀ i ∈ List.range 4,BaseCheckAt 28 (52+i):=by decide +kernel

theorem br28p14:∀ i ∈ List.range 4,BaseCheckAt 28 (56+i):=by decide +kernel

theorem br28p15:∀ i ∈ List.range 4,BaseCheckAt 28 (60+i):=by decide +kernel



theorem br28p16:∀ i ∈ List.range 4,BaseCheckAt 28 (64+i):=by decide +kernel

theorem br28p17:∀ i ∈ List.range 4,BaseCheckAt 28 (68+i):=by decide +kernel

theorem br28p18:∀ i ∈ List.range 4,BaseCheckAt 28 (72+i):=by decide +kernel

theorem br28p19:∀ i ∈ List.range 4,BaseCheckAt 28 (76+i):=by decide +kernel

theorem br28p20:∀ i ∈ List.range 4,BaseCheckAt 28 (80+i):=by decide +kernel

theorem br28p21:∀ i ∈ List.range 4,BaseCheckAt 28 (84+i):=by decide +kernel

theorem br28p22:∀ i ∈ List.range 4,BaseCheckAt 28 (88+i):=by decide +kernel

theorem br28p23:∀ i ∈ List.range 4,BaseCheckAt 28 (92+i):=by decide +kernel

theorem br28p24:∀ i ∈ List.range 4,BaseCheckAt 28 (96+i):=by decide +kernel

theorem br28p25:∀ i ∈ List.range 4,BaseCheckAt 28 (100+i):=by decide +kernel

theorem br28p26:∀ i ∈ List.range 4,BaseCheckAt 28 (104+i):=by decide +kernel

theorem br28p27:∀ i ∈ List.range 4,BaseCheckAt 28 (108+i):=by decide +kernel

theorem br28p28:∀ i ∈ List.range 3,BaseCheckAt 28 (112+i):=by decide +kernel



theorem cr28:∀ V ∈ List.range 115,CorrectAt 28 V:=by
  intro V hV
  have hv:V < 115:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr28p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr28p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr28p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr28p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr28p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr28p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr28p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr28p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr28p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr28p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr28p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr28p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr28p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr28p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr28p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr28:∀ V ∈ List.range 115,ZeroCheckAt 28 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 28 V (by omega) (by omega) (by omega)
theorem sr28:∀ V ∈ List.range 115,StrictCheckAt 28 V:=by
  intro V hV
  have hv:V < 115:=List.mem_range.mp hV
  by_cases h0_115:V < 57
  · by_cases h0_57:V < 28
    · by_cases h0_28:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr28p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr28p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr28p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr28p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr28p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr28p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr28p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr28p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr28p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr28p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr28p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr28p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr28p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr28p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_28:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr28p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr28p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr28p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr28p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr28p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr28p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr28p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_28:V < 24
          · by_cases h21_24:V < 22
            · have h:=sr28p21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr28p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr28p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr28p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr28p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr28p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr28p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
    · by_cases h28_57:V < 42
      · by_cases h28_42:V < 35
        · by_cases h28_35:V < 31
          · by_cases h28_31:V < 29
            · have h:=sr28p28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr28p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr28p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have h:=sr28p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr28p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
            · by_cases h33_35:V < 34
              · have h:=sr28p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr28p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
        · by_cases h35_42:V < 38
          · by_cases h35_38:V < 36
            · have h:=sr28p35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
            · by_cases h36_38:V < 37
              · have h:=sr28p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr28p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have h:=sr28p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr28p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
            · by_cases h40_42:V < 41
              · have h:=sr28p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr28p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
      · by_cases h42_57:V < 49
        · by_cases h42_49:V < 45
          · by_cases h42_45:V < 43
            · have h:=sr28p42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr28p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr28p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr28p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr28p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr28p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr28p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h49_57:V < 53
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have h:=sr28p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr28p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
            · by_cases h51_53:V < 52
              · have h:=sr28p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr28p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have h:=sr28p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr28p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
            · by_cases h55_57:V < 56
              · have h:=sr28p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr28p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h57_115:V < 86
    · by_cases h57_86:V < 71
      · by_cases h57_71:V < 64
        · by_cases h57_64:V < 60
          · by_cases h57_60:V < 58
            · have h:=sr28p57 (V-57) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
            · by_cases h58_60:V < 59
              · have h:=sr28p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr28p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
          · by_cases h60_64:V < 62
            · by_cases h60_62:V < 61
              · have h:=sr28p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr28p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
            · by_cases h62_64:V < 63
              · have h:=sr28p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr28p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
        · by_cases h64_71:V < 67
          · by_cases h64_67:V < 65
            · have h:=sr28p64 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
            · by_cases h65_67:V < 66
              · have h:=sr28p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr28p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have h:=sr28p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr28p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
            · by_cases h69_71:V < 70
              · have h:=sr28p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr28p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
      · by_cases h71_86:V < 78
        · by_cases h71_78:V < 74
          · by_cases h71_74:V < 72
            · have h:=sr28p71 (V-71) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
            · by_cases h72_74:V < 73
              · have h:=sr28p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr28p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have h:=sr28p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr28p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
            · by_cases h76_78:V < 77
              · have h:=sr28p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr28p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
        · by_cases h78_86:V < 82
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have h:=sr28p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr28p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
            · by_cases h80_82:V < 81
              · have h:=sr28p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr28p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have h:=sr28p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr28p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
            · by_cases h84_86:V < 85
              · have h:=sr28p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr28p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
    · by_cases h86_115:V < 100
      · by_cases h86_100:V < 93
        · by_cases h86_93:V < 89
          · by_cases h86_89:V < 87
            · have h:=sr28p86 (V-86) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
            · by_cases h87_89:V < 88
              · have h:=sr28p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr28p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · by_cases h89_93:V < 91
            · by_cases h89_91:V < 90
              · have h:=sr28p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr28p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
            · by_cases h91_93:V < 92
              · have h:=sr28p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr28p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
        · by_cases h93_100:V < 96
          · by_cases h93_96:V < 94
            · have h:=sr28p93 (V-93) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
            · by_cases h94_96:V < 95
              · have h:=sr28p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr28p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have h:=sr28p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr28p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
            · by_cases h98_100:V < 99
              · have h:=sr28p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr28p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
      · by_cases h100_115:V < 107
        · by_cases h100_107:V < 103
          · by_cases h100_103:V < 101
            · have h:=sr28p100 (V-100) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
            · by_cases h101_103:V < 102
              · have h:=sr28p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr28p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have h:=sr28p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr28p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
            · by_cases h105_107:V < 106
              · have h:=sr28p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr28p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
        · by_cases h107_115:V < 111
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have h:=sr28p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr28p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
            · by_cases h109_111:V < 110
              · have h:=sr28p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr28p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have h:=sr28p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr28p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
            · by_cases h113_115:V < 114
              · have h:=sr28p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr28p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h

theorem br28:∀ V ∈ List.range 115,BaseCheckAt 28 V:=by
  intro V hV
  have hv:V < 115:=List.mem_range.mp hV
  by_cases h0_29:V < 56
  · by_cases h0_14:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br28p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br28p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br28p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br28p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br28p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br28p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br28p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_14:V < 40
      · by_cases h7_10:V < 32
        · have h:=br28p7 (V-28) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
        · by_cases h8_10:V < 36
          · have h:=br28p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br28p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
      · by_cases h10_14:V < 48
        · by_cases h10_12:V < 44
          · have h:=br28p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br28p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
        · by_cases h12_14:V < 52
          · have h:=br28p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br28p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
  · by_cases h14_29:V < 84
    · by_cases h14_21:V < 68
      · by_cases h14_17:V < 60
        · have h:=br28p14 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · by_cases h15_17:V < 64
          · have h:=br28p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br28p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br28p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br28p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br28p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br28p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h21_29:V < 100
      · by_cases h21_25:V < 92
        · by_cases h21_23:V < 88
          · have h:=br28p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br28p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h23_25:V < 96
          · have h:=br28p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br28p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h25_29:V < 108
        · by_cases h25_27:V < 104
          · have h:=br28p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br28p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h27_29:V < 112
          · have h:=br28p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br28p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
