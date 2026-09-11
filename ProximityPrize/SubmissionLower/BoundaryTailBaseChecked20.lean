import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

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

theorem br20p0:∀ i ∈ List.range 4,BaseCheckAt 20 (0+i):=by decide +kernel

theorem br20p1:∀ i ∈ List.range 4,BaseCheckAt 20 (4+i):=by decide +kernel

theorem br20p2:∀ i ∈ List.range 4,BaseCheckAt 20 (8+i):=by decide +kernel

theorem br20p3:∀ i ∈ List.range 4,BaseCheckAt 20 (12+i):=by decide +kernel

theorem br20p4:∀ i ∈ List.range 4,BaseCheckAt 20 (16+i):=by decide +kernel

theorem br20p5:∀ i ∈ List.range 4,BaseCheckAt 20 (20+i):=by decide +kernel

theorem br20p6:∀ i ∈ List.range 4,BaseCheckAt 20 (24+i):=by decide +kernel

theorem br20p7:∀ i ∈ List.range 4,BaseCheckAt 20 (28+i):=by decide +kernel

theorem br20p8:∀ i ∈ List.range 4,BaseCheckAt 20 (32+i):=by decide +kernel

theorem br20p9:∀ i ∈ List.range 4,BaseCheckAt 20 (36+i):=by decide +kernel

theorem br20p10:∀ i ∈ List.range 4,BaseCheckAt 20 (40+i):=by decide +kernel

theorem br20p11:∀ i ∈ List.range 4,BaseCheckAt 20 (44+i):=by decide +kernel

theorem br20p12:∀ i ∈ List.range 4,BaseCheckAt 20 (48+i):=by decide +kernel

theorem br20p13:∀ i ∈ List.range 4,BaseCheckAt 20 (52+i):=by decide +kernel

theorem br20p14:∀ i ∈ List.range 4,BaseCheckAt 20 (56+i):=by decide +kernel

theorem br20p15:∀ i ∈ List.range 4,BaseCheckAt 20 (60+i):=by decide +kernel



theorem br20p16:∀ i ∈ List.range 4,BaseCheckAt 20 (64+i):=by decide +kernel

theorem br20p17:∀ i ∈ List.range 4,BaseCheckAt 20 (68+i):=by decide +kernel

theorem br20p18:∀ i ∈ List.range 4,BaseCheckAt 20 (72+i):=by decide +kernel

theorem br20p19:∀ i ∈ List.range 4,BaseCheckAt 20 (76+i):=by decide +kernel

theorem br20p20:∀ i ∈ List.range 4,BaseCheckAt 20 (80+i):=by decide +kernel

theorem br20p21:∀ i ∈ List.range 4,BaseCheckAt 20 (84+i):=by decide +kernel

theorem br20p22:∀ i ∈ List.range 4,BaseCheckAt 20 (88+i):=by decide +kernel

theorem br20p23:∀ i ∈ List.range 4,BaseCheckAt 20 (92+i):=by decide +kernel

theorem br20p24:∀ i ∈ List.range 4,BaseCheckAt 20 (96+i):=by decide +kernel

theorem br20p25:∀ i ∈ List.range 4,BaseCheckAt 20 (100+i):=by decide +kernel

theorem br20p26:∀ i ∈ List.range 4,BaseCheckAt 20 (104+i):=by decide +kernel

theorem br20p27:∀ i ∈ List.range 4,BaseCheckAt 20 (108+i):=by decide +kernel

theorem br20p28:∀ i ∈ List.range 4,BaseCheckAt 20 (112+i):=by decide +kernel

theorem br20p29:∀ i ∈ List.range 4,BaseCheckAt 20 (116+i):=by decide +kernel

theorem br20p30:∀ i ∈ List.range 3,BaseCheckAt 20 (120+i):=by decide +kernel



theorem cr20:∀ V ∈ List.range 123,CorrectAt 20 V:=by
  intro V hV
  have hv:V < 123:=List.mem_range.mp hV
  by_cases h0_16:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr20p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr20p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr20p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr20p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr20p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr20p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr20p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr20p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_16:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr20p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr20p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr20p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr20p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_16:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr20p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr20p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_16:V < 120
        · have h:=cr20p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · have h:=cr20p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem zr20:∀ V ∈ List.range 123,ZeroCheckAt 20 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 20 V (by omega) (by omega) (by omega)
theorem sr20:∀ V ∈ List.range 123,StrictCheckAt 20 V:=by
  intro V hV
  have hv:V < 123:=List.mem_range.mp hV
  by_cases h0_123:V < 61
  · by_cases h0_61:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr20p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr20p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr20p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr20p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr20p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr20p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr20p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr20p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr20p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr20p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr20p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr20p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr20p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr20p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr20p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have h:=sr20p15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
            · by_cases h16_18:V < 17
              · have h:=sr20p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr20p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have h:=sr20p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr20p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
            · by_cases h20_22:V < 21
              · have h:=sr20p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr20p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have h:=sr20p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr20p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
            · by_cases h24_26:V < 25
              · have h:=sr20p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr20p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have h:=sr20p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr20p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
            · by_cases h28_30:V < 29
              · have h:=sr20p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr20p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
    · by_cases h30_61:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have h:=sr20p30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
            · by_cases h31_33:V < 32
              · have h:=sr20p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr20p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have h:=sr20p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr20p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
            · by_cases h35_37:V < 36
              · have h:=sr20p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr20p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have h:=sr20p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr20p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
            · by_cases h39_41:V < 40
              · have h:=sr20p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr20p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have h:=sr20p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr20p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr20p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr20p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h45_61:V < 53
        · by_cases h45_53:V < 49
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr20p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr20p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr20p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr20p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have h:=sr20p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr20p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
            · by_cases h51_53:V < 52
              · have h:=sr20p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr20p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h53_61:V < 57
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have h:=sr20p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr20p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
            · by_cases h55_57:V < 56
              · have h:=sr20p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr20p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have h:=sr20p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr20p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
            · by_cases h59_61:V < 60
              · have h:=sr20p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr20p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h61_123:V < 92
    · by_cases h61_92:V < 76
      · by_cases h61_76:V < 68
        · by_cases h61_68:V < 64
          · by_cases h61_64:V < 62
            · have h:=sr20p61 (V-61) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
            · by_cases h62_64:V < 63
              · have h:=sr20p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr20p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
          · by_cases h64_68:V < 66
            · by_cases h64_66:V < 65
              · have h:=sr20p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr20p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
            · by_cases h66_68:V < 67
              · have h:=sr20p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr20p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
        · by_cases h68_76:V < 72
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have h:=sr20p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr20p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
            · by_cases h70_72:V < 71
              · have h:=sr20p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr20p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have h:=sr20p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr20p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
            · by_cases h74_76:V < 75
              · have h:=sr20p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr20p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
      · by_cases h76_92:V < 84
        · by_cases h76_84:V < 80
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have h:=sr20p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr20p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
            · by_cases h78_80:V < 79
              · have h:=sr20p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr20p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have h:=sr20p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr20p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
            · by_cases h82_84:V < 83
              · have h:=sr20p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr20p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
        · by_cases h84_92:V < 88
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have h:=sr20p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr20p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
            · by_cases h86_88:V < 87
              · have h:=sr20p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr20p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have h:=sr20p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr20p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
            · by_cases h90_92:V < 91
              · have h:=sr20p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr20p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
    · by_cases h92_123:V < 107
      · by_cases h92_107:V < 99
        · by_cases h92_99:V < 95
          · by_cases h92_95:V < 93
            · have h:=sr20p92 (V-92) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
            · by_cases h93_95:V < 94
              · have h:=sr20p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr20p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
          · by_cases h95_99:V < 97
            · by_cases h95_97:V < 96
              · have h:=sr20p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr20p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
            · by_cases h97_99:V < 98
              · have h:=sr20p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr20p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
        · by_cases h99_107:V < 103
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have h:=sr20p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr20p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
            · by_cases h101_103:V < 102
              · have h:=sr20p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr20p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have h:=sr20p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr20p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
            · by_cases h105_107:V < 106
              · have h:=sr20p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr20p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
      · by_cases h107_123:V < 115
        · by_cases h107_115:V < 111
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have h:=sr20p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr20p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
            · by_cases h109_111:V < 110
              · have h:=sr20p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr20p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have h:=sr20p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr20p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
            · by_cases h113_115:V < 114
              · have h:=sr20p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr20p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
        · by_cases h115_123:V < 119
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have h:=sr20p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr20p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
            · by_cases h117_119:V < 118
              · have h:=sr20p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
              · have h:=sr20p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have h:=sr20p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
              · have h:=sr20p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
            · by_cases h121_123:V < 122
              · have h:=sr20p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
              · have h:=sr20p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h

theorem br20:∀ V ∈ List.range 123,BaseCheckAt 20 V:=by
  intro V hV
  have hv:V < 123:=List.mem_range.mp hV
  by_cases h0_31:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br20p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br20p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br20p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br20p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br20p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br20p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br20p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br20p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br20p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br20p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br20p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br20p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br20p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br20p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br20p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_31:V < 92
    · by_cases h15_23:V < 76
      · by_cases h15_19:V < 68
        · by_cases h15_17:V < 64
          · have h:=br20p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br20p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · by_cases h17_19:V < 72
          · have h:=br20p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br20p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h19_23:V < 84
        · by_cases h19_21:V < 80
          · have h:=br20p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br20p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · by_cases h21_23:V < 88
          · have h:=br20p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br20p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h23_31:V < 108
      · by_cases h23_27:V < 100
        · by_cases h23_25:V < 96
          · have h:=br20p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br20p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · by_cases h25_27:V < 104
          · have h:=br20p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br20p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h27_31:V < 116
        · by_cases h27_29:V < 112
          · have h:=br20p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br20p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h29_31:V < 120
          · have h:=br20p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · have h:=br20p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
