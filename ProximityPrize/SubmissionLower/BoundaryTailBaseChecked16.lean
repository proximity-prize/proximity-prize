import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

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

theorem br16p0:∀ i ∈ List.range 4,BaseCheckAt 16 (0+i):=by decide +kernel

theorem br16p1:∀ i ∈ List.range 4,BaseCheckAt 16 (4+i):=by decide +kernel

theorem br16p2:∀ i ∈ List.range 4,BaseCheckAt 16 (8+i):=by decide +kernel

theorem br16p3:∀ i ∈ List.range 4,BaseCheckAt 16 (12+i):=by decide +kernel

theorem br16p4:∀ i ∈ List.range 4,BaseCheckAt 16 (16+i):=by decide +kernel

theorem br16p5:∀ i ∈ List.range 4,BaseCheckAt 16 (20+i):=by decide +kernel

theorem br16p6:∀ i ∈ List.range 4,BaseCheckAt 16 (24+i):=by decide +kernel

theorem br16p7:∀ i ∈ List.range 4,BaseCheckAt 16 (28+i):=by decide +kernel

theorem br16p8:∀ i ∈ List.range 4,BaseCheckAt 16 (32+i):=by decide +kernel

theorem br16p9:∀ i ∈ List.range 4,BaseCheckAt 16 (36+i):=by decide +kernel

theorem br16p10:∀ i ∈ List.range 4,BaseCheckAt 16 (40+i):=by decide +kernel

theorem br16p11:∀ i ∈ List.range 4,BaseCheckAt 16 (44+i):=by decide +kernel

theorem br16p12:∀ i ∈ List.range 4,BaseCheckAt 16 (48+i):=by decide +kernel

theorem br16p13:∀ i ∈ List.range 4,BaseCheckAt 16 (52+i):=by decide +kernel

theorem br16p14:∀ i ∈ List.range 4,BaseCheckAt 16 (56+i):=by decide +kernel

theorem br16p15:∀ i ∈ List.range 4,BaseCheckAt 16 (60+i):=by decide +kernel



theorem br16p16:∀ i ∈ List.range 4,BaseCheckAt 16 (64+i):=by decide +kernel

theorem br16p17:∀ i ∈ List.range 4,BaseCheckAt 16 (68+i):=by decide +kernel

theorem br16p18:∀ i ∈ List.range 4,BaseCheckAt 16 (72+i):=by decide +kernel

theorem br16p19:∀ i ∈ List.range 4,BaseCheckAt 16 (76+i):=by decide +kernel

theorem br16p20:∀ i ∈ List.range 4,BaseCheckAt 16 (80+i):=by decide +kernel

theorem br16p21:∀ i ∈ List.range 4,BaseCheckAt 16 (84+i):=by decide +kernel

theorem br16p22:∀ i ∈ List.range 4,BaseCheckAt 16 (88+i):=by decide +kernel

theorem br16p23:∀ i ∈ List.range 4,BaseCheckAt 16 (92+i):=by decide +kernel

theorem br16p24:∀ i ∈ List.range 4,BaseCheckAt 16 (96+i):=by decide +kernel

theorem br16p25:∀ i ∈ List.range 4,BaseCheckAt 16 (100+i):=by decide +kernel

theorem br16p26:∀ i ∈ List.range 4,BaseCheckAt 16 (104+i):=by decide +kernel

theorem br16p27:∀ i ∈ List.range 4,BaseCheckAt 16 (108+i):=by decide +kernel

theorem br16p28:∀ i ∈ List.range 4,BaseCheckAt 16 (112+i):=by decide +kernel

theorem br16p29:∀ i ∈ List.range 4,BaseCheckAt 16 (116+i):=by decide +kernel

theorem br16p30:∀ i ∈ List.range 4,BaseCheckAt 16 (120+i):=by decide +kernel

theorem br16p31:∀ i ∈ List.range 3,BaseCheckAt 16 (124+i):=by decide +kernel



theorem cr16:∀ V ∈ List.range 127,CorrectAt 16 V:=by
  intro V hV
  have hv:V < 127:=List.mem_range.mp hV
  by_cases h0_16:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr16p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr16p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr16p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr16p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr16p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr16p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr16p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr16p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_16:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr16p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr16p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr16p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr16p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_16:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr16p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr16p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_16:V < 120
        · have h:=cr16p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · have h:=cr16p15 (V-120) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h

theorem zr16:∀ V ∈ List.range 127,ZeroCheckAt 16 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 16 V (by omega) (by omega) (by omega)
theorem sr16:∀ V ∈ List.range 127,StrictCheckAt 16 V:=by
  intro V hV
  have hv:V < 127:=List.mem_range.mp hV
  by_cases h0_127:V < 63
  · by_cases h0_63:V < 31
    · by_cases h0_31:V < 15
      · by_cases h0_15:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr16p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr16p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr16p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr16p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr16p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr16p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr16p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_15:V < 11
          · by_cases h7_11:V < 9
            · by_cases h7_9:V < 8
              · have h:=sr16p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
              · have h:=sr16p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
            · by_cases h9_11:V < 10
              · have h:=sr16p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
              · have h:=sr16p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
          · by_cases h11_15:V < 13
            · by_cases h11_13:V < 12
              · have h:=sr16p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
              · have h:=sr16p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
            · by_cases h13_15:V < 14
              · have h:=sr16p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
              · have h:=sr16p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
      · by_cases h15_31:V < 23
        · by_cases h15_23:V < 19
          · by_cases h15_19:V < 17
            · by_cases h15_17:V < 16
              · have h:=sr16p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr16p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
            · by_cases h17_19:V < 18
              · have h:=sr16p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr16p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
          · by_cases h19_23:V < 21
            · by_cases h19_21:V < 20
              · have h:=sr16p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr16p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
            · by_cases h21_23:V < 22
              · have h:=sr16p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr16p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
        · by_cases h23_31:V < 27
          · by_cases h23_27:V < 25
            · by_cases h23_25:V < 24
              · have h:=sr16p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr16p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
            · by_cases h25_27:V < 26
              · have h:=sr16p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr16p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
          · by_cases h27_31:V < 29
            · by_cases h27_29:V < 28
              · have h:=sr16p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr16p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr16p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr16p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
    · by_cases h31_63:V < 47
      · by_cases h31_47:V < 39
        · by_cases h31_39:V < 35
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have h:=sr16p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr16p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
            · by_cases h33_35:V < 34
              · have h:=sr16p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr16p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
          · by_cases h35_39:V < 37
            · by_cases h35_37:V < 36
              · have h:=sr16p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr16p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
            · by_cases h37_39:V < 38
              · have h:=sr16p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr16p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
        · by_cases h39_47:V < 43
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have h:=sr16p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr16p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
            · by_cases h41_43:V < 42
              · have h:=sr16p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr16p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
          · by_cases h43_47:V < 45
            · by_cases h43_45:V < 44
              · have h:=sr16p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr16p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
            · by_cases h45_47:V < 46
              · have h:=sr16p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr16p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
      · by_cases h47_63:V < 55
        · by_cases h47_55:V < 51
          · by_cases h47_51:V < 49
            · by_cases h47_49:V < 48
              · have h:=sr16p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr16p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
            · by_cases h49_51:V < 50
              · have h:=sr16p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr16p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have h:=sr16p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr16p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
            · by_cases h53_55:V < 54
              · have h:=sr16p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr16p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
        · by_cases h55_63:V < 59
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have h:=sr16p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr16p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
            · by_cases h57_59:V < 58
              · have h:=sr16p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr16p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have h:=sr16p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr16p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · by_cases h61_63:V < 62
              · have h:=sr16p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr16p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
  · by_cases h63_127:V < 95
    · by_cases h63_95:V < 79
      · by_cases h63_79:V < 71
        · by_cases h63_71:V < 67
          · by_cases h63_67:V < 65
            · by_cases h63_65:V < 64
              · have h:=sr16p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr16p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
            · by_cases h65_67:V < 66
              · have h:=sr16p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr16p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have h:=sr16p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr16p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
            · by_cases h69_71:V < 70
              · have h:=sr16p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr16p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
        · by_cases h71_79:V < 75
          · by_cases h71_75:V < 73
            · by_cases h71_73:V < 72
              · have h:=sr16p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr16p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
            · by_cases h73_75:V < 74
              · have h:=sr16p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr16p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have h:=sr16p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr16p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
            · by_cases h77_79:V < 78
              · have h:=sr16p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr16p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
      · by_cases h79_95:V < 87
        · by_cases h79_87:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have h:=sr16p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr16p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
            · by_cases h81_83:V < 82
              · have h:=sr16p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr16p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have h:=sr16p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr16p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
            · by_cases h85_87:V < 86
              · have h:=sr16p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr16p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
        · by_cases h87_95:V < 91
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have h:=sr16p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr16p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
            · by_cases h89_91:V < 90
              · have h:=sr16p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr16p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
          · by_cases h91_95:V < 93
            · by_cases h91_93:V < 92
              · have h:=sr16p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
              · have h:=sr16p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
            · by_cases h93_95:V < 94
              · have h:=sr16p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr16p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
    · by_cases h95_127:V < 111
      · by_cases h95_111:V < 103
        · by_cases h95_103:V < 99
          · by_cases h95_99:V < 97
            · by_cases h95_97:V < 96
              · have h:=sr16p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr16p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
            · by_cases h97_99:V < 98
              · have h:=sr16p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr16p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have h:=sr16p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr16p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
            · by_cases h101_103:V < 102
              · have h:=sr16p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr16p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
        · by_cases h103_111:V < 107
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have h:=sr16p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr16p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
            · by_cases h105_107:V < 106
              · have h:=sr16p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr16p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have h:=sr16p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr16p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
            · by_cases h109_111:V < 110
              · have h:=sr16p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr16p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
      · by_cases h111_127:V < 119
        · by_cases h111_119:V < 115
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have h:=sr16p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr16p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
            · by_cases h113_115:V < 114
              · have h:=sr16p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr16p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have h:=sr16p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr16p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
            · by_cases h117_119:V < 118
              · have h:=sr16p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
              · have h:=sr16p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
        · by_cases h119_127:V < 123
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have h:=sr16p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
              · have h:=sr16p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
            · by_cases h121_123:V < 122
              · have h:=sr16p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
              · have h:=sr16p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
          · by_cases h123_127:V < 125
            · by_cases h123_125:V < 124
              · have h:=sr16p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
              · have h:=sr16p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
            · by_cases h125_127:V < 126
              · have h:=sr16p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
              · have h:=sr16p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h

theorem br16:∀ V ∈ List.range 127,BaseCheckAt 16 V:=by
  intro V hV
  have hv:V < 127:=List.mem_range.mp hV
  by_cases h0_32:V < 64
  · by_cases h0_16:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br16p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br16p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br16p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br16p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br16p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br16p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br16p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br16p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_16:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br16p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br16p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br16p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br16p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_16:V < 56
        · by_cases h12_14:V < 52
          · have h:=br16p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br16p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_16:V < 60
          · have h:=br16p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · have h:=br16p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h16_32:V < 96
    · by_cases h16_24:V < 80
      · by_cases h16_20:V < 72
        · by_cases h16_18:V < 68
          · have h:=br16p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br16p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h18_20:V < 76
          · have h:=br16p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br16p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h20_24:V < 88
        · by_cases h20_22:V < 84
          · have h:=br16p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br16p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br16p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br16p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h24_32:V < 112
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br16p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br16p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br16p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br16p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h28_32:V < 120
        · by_cases h28_30:V < 116
          · have h:=br16p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br16p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h30_32:V < 124
          · have h:=br16p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=br16p31 (V-124) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
