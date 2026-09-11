import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr25p0:∀ i ∈ List.range 8,CorrectAt 25 (0+i):=by decide +kernel

theorem cr25p1:∀ i ∈ List.range 8,CorrectAt 25 (8+i):=by decide +kernel

theorem cr25p2:∀ i ∈ List.range 8,CorrectAt 25 (16+i):=by decide +kernel

theorem cr25p3:∀ i ∈ List.range 8,CorrectAt 25 (24+i):=by decide +kernel

theorem cr25p4:∀ i ∈ List.range 8,CorrectAt 25 (32+i):=by decide +kernel

theorem cr25p5:∀ i ∈ List.range 8,CorrectAt 25 (40+i):=by decide +kernel

theorem cr25p6:∀ i ∈ List.range 8,CorrectAt 25 (48+i):=by decide +kernel

theorem cr25p7:∀ i ∈ List.range 8,CorrectAt 25 (56+i):=by decide +kernel

theorem cr25p8:∀ i ∈ List.range 8,CorrectAt 25 (64+i):=by decide +kernel

theorem cr25p9:∀ i ∈ List.range 8,CorrectAt 25 (72+i):=by decide +kernel

theorem cr25p10:∀ i ∈ List.range 8,CorrectAt 25 (80+i):=by decide +kernel

theorem cr25p11:∀ i ∈ List.range 8,CorrectAt 25 (88+i):=by decide +kernel

theorem cr25p12:∀ i ∈ List.range 8,CorrectAt 25 (96+i):=by decide +kernel

theorem cr25p13:∀ i ∈ List.range 8,CorrectAt 25 (104+i):=by decide +kernel

theorem cr25p14:∀ i ∈ List.range 6,CorrectAt 25 (112+i):=by decide +kernel

theorem sr25p0:∀ i ∈ List.range 1,StrictCheckAt 25 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 0) 25 0:=by decide +kernel
  have hfast:StrictAtFast (row 25 0) 25 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 0) 25 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 0) 25 0 hvalid hfast

theorem sr25p1:∀ i ∈ List.range 1,StrictCheckAt 25 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 1) 25 1:=by decide +kernel
  have hfast:StrictAtFast (row 25 1) 25 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 1) 25 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 1) 25 1 hvalid hfast

theorem sr25p2:∀ i ∈ List.range 1,StrictCheckAt 25 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 2) 25 2:=by decide +kernel
  have hfast:StrictAtFast (row 25 2) 25 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 2) 25 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 2) 25 2 hvalid hfast

theorem sr25p3:∀ i ∈ List.range 1,StrictCheckAt 25 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 3) 25 3:=by decide +kernel
  have hfast:StrictAtFast (row 25 3) 25 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 3) 25 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 3) 25 3 hvalid hfast

theorem sr25p4:∀ i ∈ List.range 1,StrictCheckAt 25 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 4) 25 4:=by decide +kernel
  have hfast:StrictAtFast (row 25 4) 25 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 4) 25 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 4) 25 4 hvalid hfast

theorem sr25p5:∀ i ∈ List.range 1,StrictCheckAt 25 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 5) 25 5:=by decide +kernel
  have hfast:StrictAtFast (row 25 5) 25 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 5) 25 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 5) 25 5 hvalid hfast

theorem sr25p6:∀ i ∈ List.range 1,StrictCheckAt 25 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 6) 25 6:=by decide +kernel
  have hfast:StrictAtFast (row 25 6) 25 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 6) 25 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 6) 25 6 hvalid hfast

theorem sr25p7:∀ i ∈ List.range 1,StrictCheckAt 25 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 7) 25 7:=by decide +kernel
  have hfast:StrictAtFast (row 25 7) 25 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 7) 25 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 7) 25 7 hvalid hfast

theorem sr25p8:∀ i ∈ List.range 1,StrictCheckAt 25 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 8) 25 8:=by decide +kernel
  have hfast:StrictAtFast (row 25 8) 25 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 8) 25 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 8) 25 8 hvalid hfast

theorem sr25p9:∀ i ∈ List.range 1,StrictCheckAt 25 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 9) 25 9:=by decide +kernel
  have hfast:StrictAtFast (row 25 9) 25 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 9) 25 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 9) 25 9 hvalid hfast

theorem sr25p10:∀ i ∈ List.range 1,StrictCheckAt 25 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 10) 25 10:=by decide +kernel
  have hfast:StrictAtFast (row 25 10) 25 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 10) 25 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 10) 25 10 hvalid hfast

theorem sr25p11:∀ i ∈ List.range 1,StrictCheckAt 25 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 11) 25 11:=by decide +kernel
  have hfast:StrictAtFast (row 25 11) 25 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 11) 25 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 11) 25 11 hvalid hfast

theorem sr25p12:∀ i ∈ List.range 1,StrictCheckAt 25 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 12) 25 12:=by decide +kernel
  have hfast:StrictAtFast (row 25 12) 25 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 12) 25 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 12) 25 12 hvalid hfast

theorem sr25p13:∀ i ∈ List.range 1,StrictCheckAt 25 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 13) 25 13:=by decide +kernel
  have hfast:StrictAtFast (row 25 13) 25 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 13) 25 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 13) 25 13 hvalid hfast

theorem sr25p14:∀ i ∈ List.range 1,StrictCheckAt 25 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 14) 25 14:=by decide +kernel
  have hfast:StrictAtFast (row 25 14) 25 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 14) 25 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 14) 25 14 hvalid hfast

theorem sr25p15:∀ i ∈ List.range 1,StrictCheckAt 25 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 15) 25 15:=by decide +kernel
  have hfast:StrictAtFast (row 25 15) 25 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 15) 25 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 15) 25 15 hvalid hfast

theorem sr25p16:∀ i ∈ List.range 1,StrictCheckAt 25 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 16) 25 16:=by decide +kernel
  have hfast:StrictAtFast (row 25 16) 25 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 16) 25 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 16) 25 16 hvalid hfast

theorem sr25p17:∀ i ∈ List.range 1,StrictCheckAt 25 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 17) 25 17:=by decide +kernel
  have hfast:StrictAtFast (row 25 17) 25 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 17) 25 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 17) 25 17 hvalid hfast

theorem sr25p18:∀ i ∈ List.range 1,StrictCheckAt 25 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 18) 25 18:=by decide +kernel
  have hfast:StrictAtFast (row 25 18) 25 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 18) 25 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 18) 25 18 hvalid hfast

theorem sr25p19:∀ i ∈ List.range 1,StrictCheckAt 25 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 19) 25 19:=by decide +kernel
  have hfast:StrictAtFast (row 25 19) 25 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 19) 25 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 19) 25 19 hvalid hfast

theorem sr25p20:∀ i ∈ List.range 1,StrictCheckAt 25 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 20) 25 20:=by decide +kernel
  have hfast:StrictAtFast (row 25 20) 25 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 20) 25 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 20) 25 20 hvalid hfast

theorem sr25p21:∀ i ∈ List.range 1,StrictCheckAt 25 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 21) 25 21:=by decide +kernel
  have hfast:StrictAtFast (row 25 21) 25 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 21) 25 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 21) 25 21 hvalid hfast

theorem sr25p22:∀ i ∈ List.range 1,StrictCheckAt 25 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 22) 25 22:=by decide +kernel
  have hfast:StrictAtFast (row 25 22) 25 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 22) 25 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 22) 25 22 hvalid hfast

theorem sr25p23:∀ i ∈ List.range 1,StrictCheckAt 25 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 23) 25 23:=by decide +kernel
  have hfast:StrictAtFast (row 25 23) 25 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 23) 25 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 23) 25 23 hvalid hfast

theorem sr25p24:∀ i ∈ List.range 1,StrictCheckAt 25 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 24) 25 24:=by decide +kernel
  have hfast:StrictAtFast (row 25 24) 25 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 24) 25 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 24) 25 24 hvalid hfast

theorem sr25p25:∀ i ∈ List.range 1,StrictCheckAt 25 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 25) 25 25:=by decide +kernel
  have hfast:StrictAtFast (row 25 25) 25 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 25) 25 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 25) 25 25 hvalid hfast

theorem sr25p26:∀ i ∈ List.range 1,StrictCheckAt 25 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 26) 25 26:=by decide +kernel
  have hfast:StrictAtFast (row 25 26) 25 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 26) 25 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 26) 25 26 hvalid hfast

theorem sr25p27:∀ i ∈ List.range 1,StrictCheckAt 25 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 27) 25 27:=by decide +kernel
  have hfast:StrictAtFast (row 25 27) 25 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 27) 25 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 27) 25 27 hvalid hfast

theorem sr25p28:∀ i ∈ List.range 1,StrictCheckAt 25 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 28) 25 28:=by decide +kernel
  have hfast:StrictAtFast (row 25 28) 25 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 28) 25 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 28) 25 28 hvalid hfast

theorem sr25p29:∀ i ∈ List.range 1,StrictCheckAt 25 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 29) 25 29:=by decide +kernel
  have hfast:StrictAtFast (row 25 29) 25 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 29) 25 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 29) 25 29 hvalid hfast

theorem sr25p30:∀ i ∈ List.range 1,StrictCheckAt 25 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 30) 25 30:=by decide +kernel
  have hfast:StrictAtFast (row 25 30) 25 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 30) 25 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 30) 25 30 hvalid hfast

theorem sr25p31:∀ i ∈ List.range 1,StrictCheckAt 25 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 31) 25 31:=by decide +kernel
  have hfast:StrictAtFast (row 25 31) 25 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 31) 25 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 31) 25 31 hvalid hfast

theorem sr25p32:∀ i ∈ List.range 1,StrictCheckAt 25 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 32) 25 32:=by decide +kernel
  have hfast:StrictAtFast (row 25 32) 25 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 32) 25 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 32) 25 32 hvalid hfast

theorem sr25p33:∀ i ∈ List.range 1,StrictCheckAt 25 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 33) 25 33:=by decide +kernel
  have hfast:StrictAtFast (row 25 33) 25 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 33) 25 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 33) 25 33 hvalid hfast

theorem sr25p34:∀ i ∈ List.range 1,StrictCheckAt 25 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 34) 25 34:=by decide +kernel
  have hfast:StrictAtFast (row 25 34) 25 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 34) 25 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 34) 25 34 hvalid hfast

theorem sr25p35:∀ i ∈ List.range 1,StrictCheckAt 25 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 35) 25 35:=by decide +kernel
  have hfast:StrictAtFast (row 25 35) 25 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 35) 25 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 35) 25 35 hvalid hfast

theorem sr25p36:∀ i ∈ List.range 1,StrictCheckAt 25 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 36) 25 36:=by decide +kernel
  have hfast:StrictAtFast (row 25 36) 25 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 36) 25 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 36) 25 36 hvalid hfast

theorem sr25p37:∀ i ∈ List.range 1,StrictCheckAt 25 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 37) 25 37:=by decide +kernel
  have hfast:StrictAtFast (row 25 37) 25 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 37) 25 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 37) 25 37 hvalid hfast

theorem sr25p38:∀ i ∈ List.range 1,StrictCheckAt 25 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 38) 25 38:=by decide +kernel
  have hfast:StrictAtFast (row 25 38) 25 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 38) 25 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 38) 25 38 hvalid hfast

theorem sr25p39:∀ i ∈ List.range 1,StrictCheckAt 25 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 39) 25 39:=by decide +kernel
  have hfast:StrictAtFast (row 25 39) 25 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 39) 25 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 39) 25 39 hvalid hfast

theorem sr25p40:∀ i ∈ List.range 1,StrictCheckAt 25 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 40) 25 40:=by decide +kernel
  have hfast:StrictAtFast (row 25 40) 25 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 40) 25 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 40) 25 40 hvalid hfast

theorem sr25p41:∀ i ∈ List.range 1,StrictCheckAt 25 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 41) 25 41:=by decide +kernel
  have hfast:StrictAtFast (row 25 41) 25 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 41) 25 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 41) 25 41 hvalid hfast

theorem sr25p42:∀ i ∈ List.range 1,StrictCheckAt 25 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 42) 25 42:=by decide +kernel
  have hfast:StrictAtFast (row 25 42) 25 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 42) 25 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 42) 25 42 hvalid hfast

theorem sr25p43:∀ i ∈ List.range 1,StrictCheckAt 25 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 43) 25 43:=by decide +kernel
  have hfast:StrictAtFast (row 25 43) 25 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 43) 25 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 43) 25 43 hvalid hfast

theorem sr25p44:∀ i ∈ List.range 1,StrictCheckAt 25 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 44) 25 44:=by decide +kernel
  have hfast:StrictAtFast (row 25 44) 25 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 44) 25 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 44) 25 44 hvalid hfast

theorem sr25p45:∀ i ∈ List.range 1,StrictCheckAt 25 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 45) 25 45:=by decide +kernel
  have hfast:StrictAtFast (row 25 45) 25 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 45) 25 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 45) 25 45 hvalid hfast

theorem sr25p46:∀ i ∈ List.range 1,StrictCheckAt 25 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 46) 25 46:=by decide +kernel
  have hfast:StrictAtFast (row 25 46) 25 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 46) 25 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 46) 25 46 hvalid hfast

theorem sr25p47:∀ i ∈ List.range 1,StrictCheckAt 25 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 47) 25 47:=by decide +kernel
  have hfast:StrictAtFast (row 25 47) 25 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 47) 25 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 47) 25 47 hvalid hfast

theorem sr25p48:∀ i ∈ List.range 1,StrictCheckAt 25 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 48) 25 48:=by decide +kernel
  have hfast:StrictAtFast (row 25 48) 25 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 48) 25 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 48) 25 48 hvalid hfast

theorem sr25p49:∀ i ∈ List.range 1,StrictCheckAt 25 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 49) 25 49:=by decide +kernel
  have hfast:StrictAtFast (row 25 49) 25 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 49) 25 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 49) 25 49 hvalid hfast

theorem sr25p50:∀ i ∈ List.range 1,StrictCheckAt 25 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 50) 25 50:=by decide +kernel
  have hfast:StrictAtFast (row 25 50) 25 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 50) 25 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 50) 25 50 hvalid hfast

theorem sr25p51:∀ i ∈ List.range 1,StrictCheckAt 25 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 51) 25 51:=by decide +kernel
  have hfast:StrictAtFast (row 25 51) 25 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 51) 25 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 51) 25 51 hvalid hfast

theorem sr25p52:∀ i ∈ List.range 1,StrictCheckAt 25 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 52) 25 52:=by decide +kernel
  have hfast:StrictAtFast (row 25 52) 25 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 52) 25 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 52) 25 52 hvalid hfast

theorem sr25p53:∀ i ∈ List.range 1,StrictCheckAt 25 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 53) 25 53:=by decide +kernel
  have hfast:StrictAtFast (row 25 53) 25 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 53) 25 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 53) 25 53 hvalid hfast

theorem sr25p54:∀ i ∈ List.range 1,StrictCheckAt 25 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 54) 25 54:=by decide +kernel
  have hfast:StrictAtFast (row 25 54) 25 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 54) 25 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 54) 25 54 hvalid hfast

theorem sr25p55:∀ i ∈ List.range 1,StrictCheckAt 25 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 55) 25 55:=by decide +kernel
  have hfast:StrictAtFast (row 25 55) 25 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 55) 25 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 55) 25 55 hvalid hfast

theorem sr25p56:∀ i ∈ List.range 1,StrictCheckAt 25 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 56) 25 56:=by decide +kernel
  have hfast:StrictAtFast (row 25 56) 25 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 56) 25 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 56) 25 56 hvalid hfast

theorem sr25p57:∀ i ∈ List.range 1,StrictCheckAt 25 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 57) 25 57:=by decide +kernel
  have hfast:StrictAtFast (row 25 57) 25 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 57) 25 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 57) 25 57 hvalid hfast

theorem sr25p58:∀ i ∈ List.range 1,StrictCheckAt 25 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 58) 25 58:=by decide +kernel
  have hfast:StrictAtFast (row 25 58) 25 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 58) 25 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 58) 25 58 hvalid hfast

theorem sr25p59:∀ i ∈ List.range 1,StrictCheckAt 25 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 59) 25 59:=by decide +kernel
  have hfast:StrictAtFast (row 25 59) 25 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 59) 25 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 59) 25 59 hvalid hfast

theorem sr25p60:∀ i ∈ List.range 1,StrictCheckAt 25 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 60) 25 60:=by decide +kernel
  have hfast:StrictAtFast (row 25 60) 25 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 60) 25 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 60) 25 60 hvalid hfast

theorem sr25p61:∀ i ∈ List.range 1,StrictCheckAt 25 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 61) 25 61:=by decide +kernel
  have hfast:StrictAtFast (row 25 61) 25 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 61) 25 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 61) 25 61 hvalid hfast

theorem sr25p62:∀ i ∈ List.range 1,StrictCheckAt 25 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 62) 25 62:=by decide +kernel
  have hfast:StrictAtFast (row 25 62) 25 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 62) 25 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 62) 25 62 hvalid hfast

theorem sr25p63:∀ i ∈ List.range 1,StrictCheckAt 25 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 63) 25 63:=by decide +kernel
  have hfast:StrictAtFast (row 25 63) 25 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 63) 25 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 63) 25 63 hvalid hfast

theorem sr25p64:∀ i ∈ List.range 1,StrictCheckAt 25 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 64) 25 64:=by decide +kernel
  have hfast:StrictAtFast (row 25 64) 25 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 64) 25 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 64) 25 64 hvalid hfast

theorem sr25p65:∀ i ∈ List.range 1,StrictCheckAt 25 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 65) 25 65:=by decide +kernel
  have hfast:StrictAtFast (row 25 65) 25 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 65) 25 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 65) 25 65 hvalid hfast

theorem sr25p66:∀ i ∈ List.range 1,StrictCheckAt 25 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 66) 25 66:=by decide +kernel
  have hfast:StrictAtFast (row 25 66) 25 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 66) 25 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 66) 25 66 hvalid hfast

theorem sr25p67:∀ i ∈ List.range 1,StrictCheckAt 25 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 67) 25 67:=by decide +kernel
  have hfast:StrictAtFast (row 25 67) 25 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 67) 25 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 67) 25 67 hvalid hfast

theorem sr25p68:∀ i ∈ List.range 1,StrictCheckAt 25 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 68) 25 68:=by decide +kernel
  have hfast:StrictAtFast (row 25 68) 25 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 68) 25 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 68) 25 68 hvalid hfast

theorem sr25p69:∀ i ∈ List.range 1,StrictCheckAt 25 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 69) 25 69:=by decide +kernel
  have hfast:StrictAtFast (row 25 69) 25 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 69) 25 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 69) 25 69 hvalid hfast

theorem sr25p70:∀ i ∈ List.range 1,StrictCheckAt 25 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 70) 25 70:=by decide +kernel
  have hfast:StrictAtFast (row 25 70) 25 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 70) 25 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 70) 25 70 hvalid hfast

theorem sr25p71:∀ i ∈ List.range 1,StrictCheckAt 25 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 71) 25 71:=by decide +kernel
  have hfast:StrictAtFast (row 25 71) 25 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 71) 25 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 71) 25 71 hvalid hfast

theorem sr25p72:∀ i ∈ List.range 1,StrictCheckAt 25 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 72) 25 72:=by decide +kernel
  have hfast:StrictAtFast (row 25 72) 25 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 72) 25 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 72) 25 72 hvalid hfast

theorem sr25p73:∀ i ∈ List.range 1,StrictCheckAt 25 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 73) 25 73:=by decide +kernel
  have hfast:StrictAtFast (row 25 73) 25 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 73) 25 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 73) 25 73 hvalid hfast

theorem sr25p74:∀ i ∈ List.range 1,StrictCheckAt 25 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 74) 25 74:=by decide +kernel
  have hfast:StrictAtFast (row 25 74) 25 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 74) 25 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 74) 25 74 hvalid hfast

theorem sr25p75:∀ i ∈ List.range 1,StrictCheckAt 25 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 75) 25 75:=by decide +kernel
  have hfast:StrictAtFast (row 25 75) 25 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 75) 25 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 75) 25 75 hvalid hfast

theorem sr25p76:∀ i ∈ List.range 1,StrictCheckAt 25 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 76) 25 76:=by decide +kernel
  have hfast:StrictAtFast (row 25 76) 25 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 76) 25 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 76) 25 76 hvalid hfast

theorem sr25p77:∀ i ∈ List.range 1,StrictCheckAt 25 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 77) 25 77:=by decide +kernel
  have hfast:StrictAtFast (row 25 77) 25 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 77) 25 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 77) 25 77 hvalid hfast

theorem sr25p78:∀ i ∈ List.range 1,StrictCheckAt 25 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 78) 25 78:=by decide +kernel
  have hfast:StrictAtFast (row 25 78) 25 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 78) 25 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 78) 25 78 hvalid hfast

theorem sr25p79:∀ i ∈ List.range 1,StrictCheckAt 25 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 79) 25 79:=by decide +kernel
  have hfast:StrictAtFast (row 25 79) 25 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 79) 25 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 79) 25 79 hvalid hfast

theorem sr25p80:∀ i ∈ List.range 1,StrictCheckAt 25 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 80) 25 80:=by decide +kernel
  have hfast:StrictAtFast (row 25 80) 25 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 80) 25 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 80) 25 80 hvalid hfast

theorem sr25p81:∀ i ∈ List.range 1,StrictCheckAt 25 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 81) 25 81:=by decide +kernel
  have hfast:StrictAtFast (row 25 81) 25 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 81) 25 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 81) 25 81 hvalid hfast

theorem sr25p82:∀ i ∈ List.range 1,StrictCheckAt 25 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 82) 25 82:=by decide +kernel
  have hfast:StrictAtFast (row 25 82) 25 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 82) 25 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 82) 25 82 hvalid hfast

theorem sr25p83:∀ i ∈ List.range 1,StrictCheckAt 25 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 83) 25 83:=by decide +kernel
  have hfast:StrictAtFast (row 25 83) 25 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 83) 25 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 83) 25 83 hvalid hfast

theorem sr25p84:∀ i ∈ List.range 1,StrictCheckAt 25 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 84) 25 84:=by decide +kernel
  have hfast:StrictAtFast (row 25 84) 25 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 84) 25 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 84) 25 84 hvalid hfast

theorem sr25p85:∀ i ∈ List.range 1,StrictCheckAt 25 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 85) 25 85:=by decide +kernel
  have hfast:StrictAtFast (row 25 85) 25 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 85) 25 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 85) 25 85 hvalid hfast

theorem sr25p86:∀ i ∈ List.range 1,StrictCheckAt 25 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 86) 25 86:=by decide +kernel
  have hfast:StrictAtFast (row 25 86) 25 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 86) 25 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 86) 25 86 hvalid hfast

theorem sr25p87:∀ i ∈ List.range 1,StrictCheckAt 25 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 87) 25 87:=by decide +kernel
  have hfast:StrictAtFast (row 25 87) 25 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 87) 25 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 87) 25 87 hvalid hfast

theorem sr25p88:∀ i ∈ List.range 1,StrictCheckAt 25 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 88) 25 88:=by decide +kernel
  have hfast:StrictAtFast (row 25 88) 25 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 88) 25 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 88) 25 88 hvalid hfast

theorem sr25p89:∀ i ∈ List.range 1,StrictCheckAt 25 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 89) 25 89:=by decide +kernel
  have hfast:StrictAtFast (row 25 89) 25 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 89) 25 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 89) 25 89 hvalid hfast

theorem sr25p90:∀ i ∈ List.range 1,StrictCheckAt 25 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 90) 25 90:=by decide +kernel
  have hfast:StrictAtFast (row 25 90) 25 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 90) 25 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 90) 25 90 hvalid hfast

theorem sr25p91:∀ i ∈ List.range 1,StrictCheckAt 25 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 91) 25 91:=by decide +kernel
  have hfast:StrictAtFast (row 25 91) 25 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 91) 25 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 91) 25 91 hvalid hfast

theorem sr25p92:∀ i ∈ List.range 1,StrictCheckAt 25 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 92) 25 92:=by decide +kernel
  have hfast:StrictAtFast (row 25 92) 25 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 92) 25 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 92) 25 92 hvalid hfast

theorem sr25p93:∀ i ∈ List.range 1,StrictCheckAt 25 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 93) 25 93:=by decide +kernel
  have hfast:StrictAtFast (row 25 93) 25 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 93) 25 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 93) 25 93 hvalid hfast

theorem sr25p94:∀ i ∈ List.range 1,StrictCheckAt 25 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 94) 25 94:=by decide +kernel
  have hfast:StrictAtFast (row 25 94) 25 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 94) 25 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 94) 25 94 hvalid hfast

theorem sr25p95:∀ i ∈ List.range 1,StrictCheckAt 25 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 95) 25 95:=by decide +kernel
  have hfast:StrictAtFast (row 25 95) 25 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 95) 25 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 95) 25 95 hvalid hfast

theorem sr25p96:∀ i ∈ List.range 1,StrictCheckAt 25 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 96) 25 96:=by decide +kernel
  have hfast:StrictAtFast (row 25 96) 25 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 96) 25 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 96) 25 96 hvalid hfast

theorem sr25p97:∀ i ∈ List.range 1,StrictCheckAt 25 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 97) 25 97:=by decide +kernel
  have hfast:StrictAtFast (row 25 97) 25 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 97) 25 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 97) 25 97 hvalid hfast

theorem sr25p98:∀ i ∈ List.range 1,StrictCheckAt 25 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 98) 25 98:=by decide +kernel
  have hfast:StrictAtFast (row 25 98) 25 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 98) 25 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 98) 25 98 hvalid hfast

theorem sr25p99:∀ i ∈ List.range 1,StrictCheckAt 25 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 99) 25 99:=by decide +kernel
  have hfast:StrictAtFast (row 25 99) 25 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 99) 25 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 99) 25 99 hvalid hfast

theorem sr25p100:∀ i ∈ List.range 1,StrictCheckAt 25 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 100) 25 100:=by decide +kernel
  have hfast:StrictAtFast (row 25 100) 25 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 100) 25 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 100) 25 100 hvalid hfast

theorem sr25p101:∀ i ∈ List.range 1,StrictCheckAt 25 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 101) 25 101:=by decide +kernel
  have hfast:StrictAtFast (row 25 101) 25 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 101) 25 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 101) 25 101 hvalid hfast

theorem sr25p102:∀ i ∈ List.range 1,StrictCheckAt 25 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 102) 25 102:=by decide +kernel
  have hfast:StrictAtFast (row 25 102) 25 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 102) 25 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 102) 25 102 hvalid hfast

theorem sr25p103:∀ i ∈ List.range 1,StrictCheckAt 25 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 103) 25 103:=by decide +kernel
  have hfast:StrictAtFast (row 25 103) 25 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 103) 25 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 103) 25 103 hvalid hfast

theorem sr25p104:∀ i ∈ List.range 1,StrictCheckAt 25 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 104) 25 104:=by decide +kernel
  have hfast:StrictAtFast (row 25 104) 25 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 104) 25 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 104) 25 104 hvalid hfast

theorem sr25p105:∀ i ∈ List.range 1,StrictCheckAt 25 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 105) 25 105:=by decide +kernel
  have hfast:StrictAtFast (row 25 105) 25 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 105) 25 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 105) 25 105 hvalid hfast

theorem sr25p106:∀ i ∈ List.range 1,StrictCheckAt 25 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 106) 25 106:=by decide +kernel
  have hfast:StrictAtFast (row 25 106) 25 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 106) 25 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 106) 25 106 hvalid hfast

theorem sr25p107:∀ i ∈ List.range 1,StrictCheckAt 25 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 107) 25 107:=by decide +kernel
  have hfast:StrictAtFast (row 25 107) 25 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 107) 25 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 107) 25 107 hvalid hfast

theorem sr25p108:∀ i ∈ List.range 1,StrictCheckAt 25 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 108) 25 108:=by decide +kernel
  have hfast:StrictAtFast (row 25 108) 25 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 108) 25 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 108) 25 108 hvalid hfast

theorem sr25p109:∀ i ∈ List.range 1,StrictCheckAt 25 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 109) 25 109:=by decide +kernel
  have hfast:StrictAtFast (row 25 109) 25 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 109) 25 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 109) 25 109 hvalid hfast

theorem sr25p110:∀ i ∈ List.range 1,StrictCheckAt 25 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 110) 25 110:=by decide +kernel
  have hfast:StrictAtFast (row 25 110) 25 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 110) 25 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 110) 25 110 hvalid hfast

theorem sr25p111:∀ i ∈ List.range 1,StrictCheckAt 25 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 111) 25 111:=by decide +kernel
  have hfast:StrictAtFast (row 25 111) 25 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 111) 25 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 111) 25 111 hvalid hfast

theorem sr25p112:∀ i ∈ List.range 1,StrictCheckAt 25 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 112) 25 112:=by decide +kernel
  have hfast:StrictAtFast (row 25 112) 25 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 112) 25 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 112) 25 112 hvalid hfast

theorem sr25p113:∀ i ∈ List.range 1,StrictCheckAt 25 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 113) 25 113:=by decide +kernel
  have hfast:StrictAtFast (row 25 113) 25 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 113) 25 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 113) 25 113 hvalid hfast

theorem sr25p114:∀ i ∈ List.range 1,StrictCheckAt 25 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 114) 25 114:=by decide +kernel
  have hfast:StrictAtFast (row 25 114) 25 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 114) 25 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 114) 25 114 hvalid hfast

theorem sr25p115:∀ i ∈ List.range 1,StrictCheckAt 25 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 115) 25 115:=by decide +kernel
  have hfast:StrictAtFast (row 25 115) 25 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 115) 25 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 115) 25 115 hvalid hfast

theorem sr25p116:∀ i ∈ List.range 1,StrictCheckAt 25 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 116) 25 116:=by decide +kernel
  have hfast:StrictAtFast (row 25 116) 25 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 116) 25 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 116) 25 116 hvalid hfast

theorem sr25p117:∀ i ∈ List.range 1,StrictCheckAt 25 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 25 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 25 117) 25 117:=by decide +kernel
  have hfast:StrictAtFast (row 25 117) 25 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 25 117) 25 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 25 117) 25 117 hvalid hfast

theorem br25p0:∀ i ∈ List.range 4,BaseCheckAt 25 (0+i):=by decide +kernel

theorem br25p1:∀ i ∈ List.range 4,BaseCheckAt 25 (4+i):=by decide +kernel

theorem br25p2:∀ i ∈ List.range 4,BaseCheckAt 25 (8+i):=by decide +kernel

theorem br25p3:∀ i ∈ List.range 4,BaseCheckAt 25 (12+i):=by decide +kernel

theorem br25p4:∀ i ∈ List.range 4,BaseCheckAt 25 (16+i):=by decide +kernel

theorem br25p5:∀ i ∈ List.range 4,BaseCheckAt 25 (20+i):=by decide +kernel

theorem br25p6:∀ i ∈ List.range 4,BaseCheckAt 25 (24+i):=by decide +kernel

theorem br25p7:∀ i ∈ List.range 4,BaseCheckAt 25 (28+i):=by decide +kernel

theorem br25p8:∀ i ∈ List.range 4,BaseCheckAt 25 (32+i):=by decide +kernel

theorem br25p9:∀ i ∈ List.range 4,BaseCheckAt 25 (36+i):=by decide +kernel

theorem br25p10:∀ i ∈ List.range 4,BaseCheckAt 25 (40+i):=by decide +kernel

theorem br25p11:∀ i ∈ List.range 4,BaseCheckAt 25 (44+i):=by decide +kernel

theorem br25p12:∀ i ∈ List.range 4,BaseCheckAt 25 (48+i):=by decide +kernel

theorem br25p13:∀ i ∈ List.range 4,BaseCheckAt 25 (52+i):=by decide +kernel

theorem br25p14:∀ i ∈ List.range 4,BaseCheckAt 25 (56+i):=by decide +kernel

theorem br25p15:∀ i ∈ List.range 4,BaseCheckAt 25 (60+i):=by decide +kernel



theorem br25p16:∀ i ∈ List.range 4,BaseCheckAt 25 (64+i):=by decide +kernel

theorem br25p17:∀ i ∈ List.range 4,BaseCheckAt 25 (68+i):=by decide +kernel

theorem br25p18:∀ i ∈ List.range 4,BaseCheckAt 25 (72+i):=by decide +kernel

theorem br25p19:∀ i ∈ List.range 4,BaseCheckAt 25 (76+i):=by decide +kernel

theorem br25p20:∀ i ∈ List.range 4,BaseCheckAt 25 (80+i):=by decide +kernel

theorem br25p21:∀ i ∈ List.range 4,BaseCheckAt 25 (84+i):=by decide +kernel

theorem br25p22:∀ i ∈ List.range 4,BaseCheckAt 25 (88+i):=by decide +kernel

theorem br25p23:∀ i ∈ List.range 4,BaseCheckAt 25 (92+i):=by decide +kernel

theorem br25p24:∀ i ∈ List.range 4,BaseCheckAt 25 (96+i):=by decide +kernel

theorem br25p25:∀ i ∈ List.range 4,BaseCheckAt 25 (100+i):=by decide +kernel

theorem br25p26:∀ i ∈ List.range 4,BaseCheckAt 25 (104+i):=by decide +kernel

theorem br25p27:∀ i ∈ List.range 4,BaseCheckAt 25 (108+i):=by decide +kernel

theorem br25p28:∀ i ∈ List.range 4,BaseCheckAt 25 (112+i):=by decide +kernel

theorem br25p29:∀ i ∈ List.range 2,BaseCheckAt 25 (116+i):=by decide +kernel



theorem cr25:∀ V ∈ List.range 118,CorrectAt 25 V:=by
  intro V hV
  have hv:V < 118:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr25p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr25p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr25p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr25p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr25p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr25p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr25p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr25p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr25p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr25p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr25p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr25p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr25p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr25p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr25p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr25:∀ V ∈ List.range 118,ZeroCheckAt 25 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 25 V (by omega) (by omega) (by omega)
theorem sr25:∀ V ∈ List.range 118,StrictCheckAt 25 V:=by
  intro V hV
  have hv:V < 118:=List.mem_range.mp hV
  by_cases h0_118:V < 59
  · by_cases h0_59:V < 29
    · by_cases h0_29:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr25p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr25p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr25p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr25p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr25p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr25p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr25p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr25p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr25p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr25p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr25p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr25p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr25p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr25p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_29:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr25p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr25p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr25p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr25p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr25p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr25p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr25p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_29:V < 25
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have h:=sr25p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr25p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
            · by_cases h23_25:V < 24
              · have h:=sr25p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr25p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have h:=sr25p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr25p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
            · by_cases h27_29:V < 28
              · have h:=sr25p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr25p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h29_59:V < 44
      · by_cases h29_44:V < 36
        · by_cases h29_36:V < 32
          · by_cases h29_32:V < 30
            · have h:=sr25p29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_32:V < 31
              · have h:=sr25p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · have h:=sr25p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have h:=sr25p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr25p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
            · by_cases h34_36:V < 35
              · have h:=sr25p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr25p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
        · by_cases h36_44:V < 40
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have h:=sr25p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr25p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
            · by_cases h38_40:V < 39
              · have h:=sr25p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr25p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have h:=sr25p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr25p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
            · by_cases h42_44:V < 43
              · have h:=sr25p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr25p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
      · by_cases h44_59:V < 51
        · by_cases h44_51:V < 47
          · by_cases h44_47:V < 45
            · have h:=sr25p44 (V-44) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
            · by_cases h45_47:V < 46
              · have h:=sr25p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr25p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
          · by_cases h47_51:V < 49
            · by_cases h47_49:V < 48
              · have h:=sr25p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr25p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
            · by_cases h49_51:V < 50
              · have h:=sr25p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr25p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
        · by_cases h51_59:V < 55
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have h:=sr25p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr25p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
            · by_cases h53_55:V < 54
              · have h:=sr25p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr25p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have h:=sr25p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr25p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
            · by_cases h57_59:V < 58
              · have h:=sr25p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr25p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
  · by_cases h59_118:V < 88
    · by_cases h59_88:V < 73
      · by_cases h59_73:V < 66
        · by_cases h59_66:V < 62
          · by_cases h59_62:V < 60
            · have h:=sr25p59 (V-59) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
            · by_cases h60_62:V < 61
              · have h:=sr25p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr25p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
          · by_cases h62_66:V < 64
            · by_cases h62_64:V < 63
              · have h:=sr25p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr25p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
            · by_cases h64_66:V < 65
              · have h:=sr25p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr25p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
        · by_cases h66_73:V < 69
          · by_cases h66_69:V < 67
            · have h:=sr25p66 (V-66) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
            · by_cases h67_69:V < 68
              · have h:=sr25p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr25p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · by_cases h69_73:V < 71
            · by_cases h69_71:V < 70
              · have h:=sr25p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr25p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
            · by_cases h71_73:V < 72
              · have h:=sr25p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr25p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h73_88:V < 80
        · by_cases h73_80:V < 76
          · by_cases h73_76:V < 74
            · have h:=sr25p73 (V-73) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
            · by_cases h74_76:V < 75
              · have h:=sr25p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr25p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
          · by_cases h76_80:V < 78
            · by_cases h76_78:V < 77
              · have h:=sr25p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr25p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
            · by_cases h78_80:V < 79
              · have h:=sr25p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr25p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
        · by_cases h80_88:V < 84
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have h:=sr25p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr25p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
            · by_cases h82_84:V < 83
              · have h:=sr25p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr25p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
          · by_cases h84_88:V < 86
            · by_cases h84_86:V < 85
              · have h:=sr25p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr25p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
            · by_cases h86_88:V < 87
              · have h:=sr25p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr25p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
    · by_cases h88_118:V < 103
      · by_cases h88_103:V < 95
        · by_cases h88_95:V < 91
          · by_cases h88_91:V < 89
            · have h:=sr25p88 (V-88) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
            · by_cases h89_91:V < 90
              · have h:=sr25p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr25p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
          · by_cases h91_95:V < 93
            · by_cases h91_93:V < 92
              · have h:=sr25p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr25p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
            · by_cases h93_95:V < 94
              · have h:=sr25p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr25p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
        · by_cases h95_103:V < 99
          · by_cases h95_99:V < 97
            · by_cases h95_97:V < 96
              · have h:=sr25p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr25p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
            · by_cases h97_99:V < 98
              · have h:=sr25p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr25p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have h:=sr25p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr25p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
            · by_cases h101_103:V < 102
              · have h:=sr25p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr25p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
      · by_cases h103_118:V < 110
        · by_cases h103_110:V < 106
          · by_cases h103_106:V < 104
            · have h:=sr25p103 (V-103) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
            · by_cases h104_106:V < 105
              · have h:=sr25p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr25p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have h:=sr25p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr25p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
            · by_cases h108_110:V < 109
              · have h:=sr25p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr25p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
        · by_cases h110_118:V < 114
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have h:=sr25p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr25p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
            · by_cases h112_114:V < 113
              · have h:=sr25p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr25p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have h:=sr25p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr25p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
            · by_cases h116_118:V < 117
              · have h:=sr25p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr25p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h

theorem br25:∀ V ∈ List.range 118,BaseCheckAt 25 V:=by
  intro V hV
  have hv:V < 118:=List.mem_range.mp hV
  by_cases h0_30:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br25p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br25p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br25p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br25p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br25p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br25p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br25p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br25p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br25p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br25p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br25p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br25p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br25p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br25p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br25p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_30:V < 88
    · by_cases h15_22:V < 72
      · by_cases h15_18:V < 64
        · have h:=br25p15 (V-60) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
        · by_cases h16_18:V < 68
          · have h:=br25p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br25p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
      · by_cases h18_22:V < 80
        · by_cases h18_20:V < 76
          · have h:=br25p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br25p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
        · by_cases h20_22:V < 84
          · have h:=br25p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br25p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
    · by_cases h22_30:V < 104
      · by_cases h22_26:V < 96
        · by_cases h22_24:V < 92
          · have h:=br25p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br25p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
        · by_cases h24_26:V < 100
          · have h:=br25p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br25p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
      · by_cases h26_30:V < 112
        · by_cases h26_28:V < 108
          · have h:=br25p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br25p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
        · by_cases h28_30:V < 116
          · have h:=br25p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br25p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
