import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

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

theorem br21p0:∀ i ∈ List.range 4,BaseCheckAt 21 (0+i):=by decide +kernel

theorem br21p1:∀ i ∈ List.range 4,BaseCheckAt 21 (4+i):=by decide +kernel

theorem br21p2:∀ i ∈ List.range 4,BaseCheckAt 21 (8+i):=by decide +kernel

theorem br21p3:∀ i ∈ List.range 4,BaseCheckAt 21 (12+i):=by decide +kernel

theorem br21p4:∀ i ∈ List.range 4,BaseCheckAt 21 (16+i):=by decide +kernel

theorem br21p5:∀ i ∈ List.range 4,BaseCheckAt 21 (20+i):=by decide +kernel

theorem br21p6:∀ i ∈ List.range 4,BaseCheckAt 21 (24+i):=by decide +kernel

theorem br21p7:∀ i ∈ List.range 4,BaseCheckAt 21 (28+i):=by decide +kernel

theorem br21p8:∀ i ∈ List.range 4,BaseCheckAt 21 (32+i):=by decide +kernel

theorem br21p9:∀ i ∈ List.range 4,BaseCheckAt 21 (36+i):=by decide +kernel

theorem br21p10:∀ i ∈ List.range 4,BaseCheckAt 21 (40+i):=by decide +kernel

theorem br21p11:∀ i ∈ List.range 4,BaseCheckAt 21 (44+i):=by decide +kernel

theorem br21p12:∀ i ∈ List.range 4,BaseCheckAt 21 (48+i):=by decide +kernel

theorem br21p13:∀ i ∈ List.range 4,BaseCheckAt 21 (52+i):=by decide +kernel

theorem br21p14:∀ i ∈ List.range 4,BaseCheckAt 21 (56+i):=by decide +kernel

theorem br21p15:∀ i ∈ List.range 4,BaseCheckAt 21 (60+i):=by decide +kernel



theorem br21p16:∀ i ∈ List.range 4,BaseCheckAt 21 (64+i):=by decide +kernel

theorem br21p17:∀ i ∈ List.range 4,BaseCheckAt 21 (68+i):=by decide +kernel

theorem br21p18:∀ i ∈ List.range 4,BaseCheckAt 21 (72+i):=by decide +kernel

theorem br21p19:∀ i ∈ List.range 4,BaseCheckAt 21 (76+i):=by decide +kernel

theorem br21p20:∀ i ∈ List.range 4,BaseCheckAt 21 (80+i):=by decide +kernel

theorem br21p21:∀ i ∈ List.range 4,BaseCheckAt 21 (84+i):=by decide +kernel

theorem br21p22:∀ i ∈ List.range 4,BaseCheckAt 21 (88+i):=by decide +kernel

theorem br21p23:∀ i ∈ List.range 4,BaseCheckAt 21 (92+i):=by decide +kernel

theorem br21p24:∀ i ∈ List.range 4,BaseCheckAt 21 (96+i):=by decide +kernel

theorem br21p25:∀ i ∈ List.range 4,BaseCheckAt 21 (100+i):=by decide +kernel

theorem br21p26:∀ i ∈ List.range 4,BaseCheckAt 21 (104+i):=by decide +kernel

theorem br21p27:∀ i ∈ List.range 4,BaseCheckAt 21 (108+i):=by decide +kernel

theorem br21p28:∀ i ∈ List.range 4,BaseCheckAt 21 (112+i):=by decide +kernel

theorem br21p29:∀ i ∈ List.range 4,BaseCheckAt 21 (116+i):=by decide +kernel

theorem br21p30:∀ i ∈ List.range 2,BaseCheckAt 21 (120+i):=by decide +kernel



theorem cr21:∀ V ∈ List.range 122,CorrectAt 21 V:=by
  intro V hV
  have hv:V < 122:=List.mem_range.mp hV
  by_cases h0_16:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr21p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr21p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr21p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr21p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr21p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr21p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr21p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr21p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_16:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr21p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr21p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr21p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr21p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_16:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr21p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr21p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_16:V < 120
        · have h:=cr21p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · have h:=cr21p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem zr21:∀ V ∈ List.range 122,ZeroCheckAt 21 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 21 V (by omega) (by omega) (by omega)
theorem sr21:∀ V ∈ List.range 122,StrictCheckAt 21 V:=by
  intro V hV
  have hv:V < 122:=List.mem_range.mp hV
  by_cases h0_122:V < 61
  · by_cases h0_61:V < 30
    · by_cases h0_30:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr21p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr21p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr21p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr21p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr21p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr21p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr21p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr21p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr21p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr21p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr21p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr21p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr21p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr21p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr21p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_30:V < 22
        · by_cases h15_22:V < 18
          · by_cases h15_18:V < 16
            · have h:=sr21p15 (V-15) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
            · by_cases h16_18:V < 17
              · have h:=sr21p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr21p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
          · by_cases h18_22:V < 20
            · by_cases h18_20:V < 19
              · have h:=sr21p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr21p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
            · by_cases h20_22:V < 21
              · have h:=sr21p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr21p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
        · by_cases h22_30:V < 26
          · by_cases h22_26:V < 24
            · by_cases h22_24:V < 23
              · have h:=sr21p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr21p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
            · by_cases h24_26:V < 25
              · have h:=sr21p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr21p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
          · by_cases h26_30:V < 28
            · by_cases h26_28:V < 27
              · have h:=sr21p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr21p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
            · by_cases h28_30:V < 29
              · have h:=sr21p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr21p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
    · by_cases h30_61:V < 45
      · by_cases h30_45:V < 37
        · by_cases h30_37:V < 33
          · by_cases h30_33:V < 31
            · have h:=sr21p30 (V-30) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
            · by_cases h31_33:V < 32
              · have h:=sr21p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr21p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have h:=sr21p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr21p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
            · by_cases h35_37:V < 36
              · have h:=sr21p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr21p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h37_45:V < 41
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have h:=sr21p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr21p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
            · by_cases h39_41:V < 40
              · have h:=sr21p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr21p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have h:=sr21p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr21p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr21p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr21p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h45_61:V < 53
        · by_cases h45_53:V < 49
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr21p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr21p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr21p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr21p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have h:=sr21p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr21p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
            · by_cases h51_53:V < 52
              · have h:=sr21p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr21p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h53_61:V < 57
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have h:=sr21p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr21p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
            · by_cases h55_57:V < 56
              · have h:=sr21p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr21p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have h:=sr21p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr21p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
            · by_cases h59_61:V < 60
              · have h:=sr21p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr21p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h61_122:V < 91
    · by_cases h61_91:V < 76
      · by_cases h61_76:V < 68
        · by_cases h61_68:V < 64
          · by_cases h61_64:V < 62
            · have h:=sr21p61 (V-61) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
            · by_cases h62_64:V < 63
              · have h:=sr21p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr21p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
          · by_cases h64_68:V < 66
            · by_cases h64_66:V < 65
              · have h:=sr21p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr21p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
            · by_cases h66_68:V < 67
              · have h:=sr21p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr21p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
        · by_cases h68_76:V < 72
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have h:=sr21p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr21p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
            · by_cases h70_72:V < 71
              · have h:=sr21p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr21p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
          · by_cases h72_76:V < 74
            · by_cases h72_74:V < 73
              · have h:=sr21p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr21p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
            · by_cases h74_76:V < 75
              · have h:=sr21p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr21p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
      · by_cases h76_91:V < 83
        · by_cases h76_83:V < 79
          · by_cases h76_79:V < 77
            · have h:=sr21p76 (V-76) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
            · by_cases h77_79:V < 78
              · have h:=sr21p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr21p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have h:=sr21p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr21p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
            · by_cases h81_83:V < 82
              · have h:=sr21p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr21p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
        · by_cases h83_91:V < 87
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have h:=sr21p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr21p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
            · by_cases h85_87:V < 86
              · have h:=sr21p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr21p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have h:=sr21p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr21p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
            · by_cases h89_91:V < 90
              · have h:=sr21p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr21p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
    · by_cases h91_122:V < 106
      · by_cases h91_106:V < 98
        · by_cases h91_98:V < 94
          · by_cases h91_94:V < 92
            · have h:=sr21p91 (V-91) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr21p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr21p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have h:=sr21p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr21p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
            · by_cases h96_98:V < 97
              · have h:=sr21p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr21p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
        · by_cases h98_106:V < 102
          · by_cases h98_102:V < 100
            · by_cases h98_100:V < 99
              · have h:=sr21p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr21p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
            · by_cases h100_102:V < 101
              · have h:=sr21p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr21p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have h:=sr21p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr21p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
            · by_cases h104_106:V < 105
              · have h:=sr21p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr21p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
      · by_cases h106_122:V < 114
        · by_cases h106_114:V < 110
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have h:=sr21p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr21p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
            · by_cases h108_110:V < 109
              · have h:=sr21p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr21p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have h:=sr21p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr21p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
            · by_cases h112_114:V < 113
              · have h:=sr21p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr21p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
        · by_cases h114_122:V < 118
          · by_cases h114_118:V < 116
            · by_cases h114_116:V < 115
              · have h:=sr21p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr21p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
            · by_cases h116_118:V < 117
              · have h:=sr21p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
              · have h:=sr21p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
          · by_cases h118_122:V < 120
            · by_cases h118_120:V < 119
              · have h:=sr21p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
              · have h:=sr21p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
            · by_cases h120_122:V < 121
              · have h:=sr21p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
              · have h:=sr21p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h

theorem br21:∀ V ∈ List.range 122,BaseCheckAt 21 V:=by
  intro V hV
  have hv:V < 122:=List.mem_range.mp hV
  by_cases h0_31:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br21p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br21p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br21p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br21p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br21p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br21p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br21p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br21p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br21p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br21p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br21p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br21p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br21p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br21p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br21p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_31:V < 92
    · by_cases h15_23:V < 76
      · by_cases h15_19:V < 68
        · by_cases h15_17:V < 64
          · have h:=br21p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br21p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · by_cases h17_19:V < 72
          · have h:=br21p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br21p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h19_23:V < 84
        · by_cases h19_21:V < 80
          · have h:=br21p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br21p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · by_cases h21_23:V < 88
          · have h:=br21p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br21p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h23_31:V < 108
      · by_cases h23_27:V < 100
        · by_cases h23_25:V < 96
          · have h:=br21p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br21p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · by_cases h25_27:V < 104
          · have h:=br21p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br21p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h27_31:V < 116
        · by_cases h27_29:V < 112
          · have h:=br21p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br21p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h29_31:V < 120
          · have h:=br21p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
          · have h:=br21p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
