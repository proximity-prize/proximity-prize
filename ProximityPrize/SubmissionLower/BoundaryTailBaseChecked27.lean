import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr27p0:∀ i ∈ List.range 8,CorrectAt 27 (0+i):=by decide +kernel

theorem cr27p1:∀ i ∈ List.range 8,CorrectAt 27 (8+i):=by decide +kernel

theorem cr27p2:∀ i ∈ List.range 8,CorrectAt 27 (16+i):=by decide +kernel

theorem cr27p3:∀ i ∈ List.range 8,CorrectAt 27 (24+i):=by decide +kernel

theorem cr27p4:∀ i ∈ List.range 8,CorrectAt 27 (32+i):=by decide +kernel

theorem cr27p5:∀ i ∈ List.range 8,CorrectAt 27 (40+i):=by decide +kernel

theorem cr27p6:∀ i ∈ List.range 8,CorrectAt 27 (48+i):=by decide +kernel

theorem cr27p7:∀ i ∈ List.range 8,CorrectAt 27 (56+i):=by decide +kernel

theorem cr27p8:∀ i ∈ List.range 8,CorrectAt 27 (64+i):=by decide +kernel

theorem cr27p9:∀ i ∈ List.range 8,CorrectAt 27 (72+i):=by decide +kernel

theorem cr27p10:∀ i ∈ List.range 8,CorrectAt 27 (80+i):=by decide +kernel

theorem cr27p11:∀ i ∈ List.range 8,CorrectAt 27 (88+i):=by decide +kernel

theorem cr27p12:∀ i ∈ List.range 8,CorrectAt 27 (96+i):=by decide +kernel

theorem cr27p13:∀ i ∈ List.range 8,CorrectAt 27 (104+i):=by decide +kernel

theorem cr27p14:∀ i ∈ List.range 4,CorrectAt 27 (112+i):=by decide +kernel

theorem sr27p0:∀ i ∈ List.range 1,StrictCheckAt 27 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 0) 27 0:=by decide +kernel
  have hfast:StrictAtFast (row 27 0) 27 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 0) 27 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 0) 27 0 hvalid hfast

theorem sr27p1:∀ i ∈ List.range 1,StrictCheckAt 27 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 1) 27 1:=by decide +kernel
  have hfast:StrictAtFast (row 27 1) 27 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 1) 27 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 1) 27 1 hvalid hfast

theorem sr27p2:∀ i ∈ List.range 1,StrictCheckAt 27 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 2) 27 2:=by decide +kernel
  have hfast:StrictAtFast (row 27 2) 27 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 2) 27 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 2) 27 2 hvalid hfast

theorem sr27p3:∀ i ∈ List.range 1,StrictCheckAt 27 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 3) 27 3:=by decide +kernel
  have hfast:StrictAtFast (row 27 3) 27 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 3) 27 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 3) 27 3 hvalid hfast

theorem sr27p4:∀ i ∈ List.range 1,StrictCheckAt 27 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 4) 27 4:=by decide +kernel
  have hfast:StrictAtFast (row 27 4) 27 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 4) 27 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 4) 27 4 hvalid hfast

theorem sr27p5:∀ i ∈ List.range 1,StrictCheckAt 27 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 5) 27 5:=by decide +kernel
  have hfast:StrictAtFast (row 27 5) 27 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 5) 27 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 5) 27 5 hvalid hfast

theorem sr27p6:∀ i ∈ List.range 1,StrictCheckAt 27 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 6) 27 6:=by decide +kernel
  have hfast:StrictAtFast (row 27 6) 27 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 6) 27 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 6) 27 6 hvalid hfast

theorem sr27p7:∀ i ∈ List.range 1,StrictCheckAt 27 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 7) 27 7:=by decide +kernel
  have hfast:StrictAtFast (row 27 7) 27 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 7) 27 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 7) 27 7 hvalid hfast

theorem sr27p8:∀ i ∈ List.range 1,StrictCheckAt 27 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 8) 27 8:=by decide +kernel
  have hfast:StrictAtFast (row 27 8) 27 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 8) 27 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 8) 27 8 hvalid hfast

theorem sr27p9:∀ i ∈ List.range 1,StrictCheckAt 27 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 9) 27 9:=by decide +kernel
  have hfast:StrictAtFast (row 27 9) 27 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 9) 27 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 9) 27 9 hvalid hfast

theorem sr27p10:∀ i ∈ List.range 1,StrictCheckAt 27 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 10) 27 10:=by decide +kernel
  have hfast:StrictAtFast (row 27 10) 27 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 10) 27 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 10) 27 10 hvalid hfast

theorem sr27p11:∀ i ∈ List.range 1,StrictCheckAt 27 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 11) 27 11:=by decide +kernel
  have hfast:StrictAtFast (row 27 11) 27 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 11) 27 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 11) 27 11 hvalid hfast

theorem sr27p12:∀ i ∈ List.range 1,StrictCheckAt 27 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 12) 27 12:=by decide +kernel
  have hfast:StrictAtFast (row 27 12) 27 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 12) 27 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 12) 27 12 hvalid hfast

theorem sr27p13:∀ i ∈ List.range 1,StrictCheckAt 27 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 13) 27 13:=by decide +kernel
  have hfast:StrictAtFast (row 27 13) 27 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 13) 27 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 13) 27 13 hvalid hfast

theorem sr27p14:∀ i ∈ List.range 1,StrictCheckAt 27 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 14) 27 14:=by decide +kernel
  have hfast:StrictAtFast (row 27 14) 27 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 14) 27 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 14) 27 14 hvalid hfast

theorem sr27p15:∀ i ∈ List.range 1,StrictCheckAt 27 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 15) 27 15:=by decide +kernel
  have hfast:StrictAtFast (row 27 15) 27 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 15) 27 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 15) 27 15 hvalid hfast

theorem sr27p16:∀ i ∈ List.range 1,StrictCheckAt 27 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 16) 27 16:=by decide +kernel
  have hfast:StrictAtFast (row 27 16) 27 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 16) 27 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 16) 27 16 hvalid hfast

theorem sr27p17:∀ i ∈ List.range 1,StrictCheckAt 27 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 17) 27 17:=by decide +kernel
  have hfast:StrictAtFast (row 27 17) 27 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 17) 27 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 17) 27 17 hvalid hfast

theorem sr27p18:∀ i ∈ List.range 1,StrictCheckAt 27 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 18) 27 18:=by decide +kernel
  have hfast:StrictAtFast (row 27 18) 27 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 18) 27 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 18) 27 18 hvalid hfast

theorem sr27p19:∀ i ∈ List.range 1,StrictCheckAt 27 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 19) 27 19:=by decide +kernel
  have hfast:StrictAtFast (row 27 19) 27 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 19) 27 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 19) 27 19 hvalid hfast

theorem sr27p20:∀ i ∈ List.range 1,StrictCheckAt 27 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 20) 27 20:=by decide +kernel
  have hfast:StrictAtFast (row 27 20) 27 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 20) 27 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 20) 27 20 hvalid hfast

theorem sr27p21:∀ i ∈ List.range 1,StrictCheckAt 27 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 21) 27 21:=by decide +kernel
  have hfast:StrictAtFast (row 27 21) 27 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 21) 27 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 21) 27 21 hvalid hfast

theorem sr27p22:∀ i ∈ List.range 1,StrictCheckAt 27 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 22) 27 22:=by decide +kernel
  have hfast:StrictAtFast (row 27 22) 27 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 22) 27 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 22) 27 22 hvalid hfast

theorem sr27p23:∀ i ∈ List.range 1,StrictCheckAt 27 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 23) 27 23:=by decide +kernel
  have hfast:StrictAtFast (row 27 23) 27 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 23) 27 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 23) 27 23 hvalid hfast

theorem sr27p24:∀ i ∈ List.range 1,StrictCheckAt 27 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 24) 27 24:=by decide +kernel
  have hfast:StrictAtFast (row 27 24) 27 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 24) 27 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 24) 27 24 hvalid hfast

theorem sr27p25:∀ i ∈ List.range 1,StrictCheckAt 27 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 25) 27 25:=by decide +kernel
  have hfast:StrictAtFast (row 27 25) 27 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 25) 27 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 25) 27 25 hvalid hfast

theorem sr27p26:∀ i ∈ List.range 1,StrictCheckAt 27 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 26) 27 26:=by decide +kernel
  have hfast:StrictAtFast (row 27 26) 27 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 26) 27 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 26) 27 26 hvalid hfast

theorem sr27p27:∀ i ∈ List.range 1,StrictCheckAt 27 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 27) 27 27:=by decide +kernel
  have hfast:StrictAtFast (row 27 27) 27 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 27) 27 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 27) 27 27 hvalid hfast

theorem sr27p28:∀ i ∈ List.range 1,StrictCheckAt 27 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 28) 27 28:=by decide +kernel
  have hfast:StrictAtFast (row 27 28) 27 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 28) 27 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 28) 27 28 hvalid hfast

theorem sr27p29:∀ i ∈ List.range 1,StrictCheckAt 27 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 29) 27 29:=by decide +kernel
  have hfast:StrictAtFast (row 27 29) 27 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 29) 27 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 29) 27 29 hvalid hfast

theorem sr27p30:∀ i ∈ List.range 1,StrictCheckAt 27 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 30) 27 30:=by decide +kernel
  have hfast:StrictAtFast (row 27 30) 27 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 30) 27 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 30) 27 30 hvalid hfast

theorem sr27p31:∀ i ∈ List.range 1,StrictCheckAt 27 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 31) 27 31:=by decide +kernel
  have hfast:StrictAtFast (row 27 31) 27 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 31) 27 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 31) 27 31 hvalid hfast

theorem sr27p32:∀ i ∈ List.range 1,StrictCheckAt 27 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 32) 27 32:=by decide +kernel
  have hfast:StrictAtFast (row 27 32) 27 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 32) 27 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 32) 27 32 hvalid hfast

theorem sr27p33:∀ i ∈ List.range 1,StrictCheckAt 27 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 33) 27 33:=by decide +kernel
  have hfast:StrictAtFast (row 27 33) 27 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 33) 27 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 33) 27 33 hvalid hfast

theorem sr27p34:∀ i ∈ List.range 1,StrictCheckAt 27 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 34) 27 34:=by decide +kernel
  have hfast:StrictAtFast (row 27 34) 27 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 34) 27 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 34) 27 34 hvalid hfast

theorem sr27p35:∀ i ∈ List.range 1,StrictCheckAt 27 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 35) 27 35:=by decide +kernel
  have hfast:StrictAtFast (row 27 35) 27 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 35) 27 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 35) 27 35 hvalid hfast

theorem sr27p36:∀ i ∈ List.range 1,StrictCheckAt 27 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 36) 27 36:=by decide +kernel
  have hfast:StrictAtFast (row 27 36) 27 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 36) 27 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 36) 27 36 hvalid hfast

theorem sr27p37:∀ i ∈ List.range 1,StrictCheckAt 27 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 37) 27 37:=by decide +kernel
  have hfast:StrictAtFast (row 27 37) 27 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 37) 27 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 37) 27 37 hvalid hfast

theorem sr27p38:∀ i ∈ List.range 1,StrictCheckAt 27 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 38) 27 38:=by decide +kernel
  have hfast:StrictAtFast (row 27 38) 27 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 38) 27 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 38) 27 38 hvalid hfast

theorem sr27p39:∀ i ∈ List.range 1,StrictCheckAt 27 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 39) 27 39:=by decide +kernel
  have hfast:StrictAtFast (row 27 39) 27 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 39) 27 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 39) 27 39 hvalid hfast

theorem sr27p40:∀ i ∈ List.range 1,StrictCheckAt 27 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 40) 27 40:=by decide +kernel
  have hfast:StrictAtFast (row 27 40) 27 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 40) 27 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 40) 27 40 hvalid hfast

theorem sr27p41:∀ i ∈ List.range 1,StrictCheckAt 27 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 41) 27 41:=by decide +kernel
  have hfast:StrictAtFast (row 27 41) 27 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 41) 27 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 41) 27 41 hvalid hfast

theorem sr27p42:∀ i ∈ List.range 1,StrictCheckAt 27 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 42) 27 42:=by decide +kernel
  have hfast:StrictAtFast (row 27 42) 27 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 42) 27 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 42) 27 42 hvalid hfast

theorem sr27p43:∀ i ∈ List.range 1,StrictCheckAt 27 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 43) 27 43:=by decide +kernel
  have hfast:StrictAtFast (row 27 43) 27 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 43) 27 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 43) 27 43 hvalid hfast

theorem sr27p44:∀ i ∈ List.range 1,StrictCheckAt 27 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 44) 27 44:=by decide +kernel
  have hfast:StrictAtFast (row 27 44) 27 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 44) 27 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 44) 27 44 hvalid hfast

theorem sr27p45:∀ i ∈ List.range 1,StrictCheckAt 27 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 45) 27 45:=by decide +kernel
  have hfast:StrictAtFast (row 27 45) 27 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 45) 27 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 45) 27 45 hvalid hfast

theorem sr27p46:∀ i ∈ List.range 1,StrictCheckAt 27 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 46) 27 46:=by decide +kernel
  have hfast:StrictAtFast (row 27 46) 27 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 46) 27 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 46) 27 46 hvalid hfast

theorem sr27p47:∀ i ∈ List.range 1,StrictCheckAt 27 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 47) 27 47:=by decide +kernel
  have hfast:StrictAtFast (row 27 47) 27 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 47) 27 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 47) 27 47 hvalid hfast

theorem sr27p48:∀ i ∈ List.range 1,StrictCheckAt 27 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 48) 27 48:=by decide +kernel
  have hfast:StrictAtFast (row 27 48) 27 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 48) 27 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 48) 27 48 hvalid hfast

theorem sr27p49:∀ i ∈ List.range 1,StrictCheckAt 27 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 49) 27 49:=by decide +kernel
  have hfast:StrictAtFast (row 27 49) 27 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 49) 27 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 49) 27 49 hvalid hfast

theorem sr27p50:∀ i ∈ List.range 1,StrictCheckAt 27 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 50) 27 50:=by decide +kernel
  have hfast:StrictAtFast (row 27 50) 27 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 50) 27 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 50) 27 50 hvalid hfast

theorem sr27p51:∀ i ∈ List.range 1,StrictCheckAt 27 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 51) 27 51:=by decide +kernel
  have hfast:StrictAtFast (row 27 51) 27 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 51) 27 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 51) 27 51 hvalid hfast

theorem sr27p52:∀ i ∈ List.range 1,StrictCheckAt 27 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 52) 27 52:=by decide +kernel
  have hfast:StrictAtFast (row 27 52) 27 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 52) 27 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 52) 27 52 hvalid hfast

theorem sr27p53:∀ i ∈ List.range 1,StrictCheckAt 27 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 53) 27 53:=by decide +kernel
  have hfast:StrictAtFast (row 27 53) 27 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 53) 27 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 53) 27 53 hvalid hfast

theorem sr27p54:∀ i ∈ List.range 1,StrictCheckAt 27 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 54) 27 54:=by decide +kernel
  have hfast:StrictAtFast (row 27 54) 27 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 54) 27 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 54) 27 54 hvalid hfast

theorem sr27p55:∀ i ∈ List.range 1,StrictCheckAt 27 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 55) 27 55:=by decide +kernel
  have hfast:StrictAtFast (row 27 55) 27 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 55) 27 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 55) 27 55 hvalid hfast

theorem sr27p56:∀ i ∈ List.range 1,StrictCheckAt 27 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 56) 27 56:=by decide +kernel
  have hfast:StrictAtFast (row 27 56) 27 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 56) 27 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 56) 27 56 hvalid hfast

theorem sr27p57:∀ i ∈ List.range 1,StrictCheckAt 27 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 57) 27 57:=by decide +kernel
  have hfast:StrictAtFast (row 27 57) 27 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 57) 27 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 57) 27 57 hvalid hfast

theorem sr27p58:∀ i ∈ List.range 1,StrictCheckAt 27 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 58) 27 58:=by decide +kernel
  have hfast:StrictAtFast (row 27 58) 27 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 58) 27 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 58) 27 58 hvalid hfast

theorem sr27p59:∀ i ∈ List.range 1,StrictCheckAt 27 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 59) 27 59:=by decide +kernel
  have hfast:StrictAtFast (row 27 59) 27 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 59) 27 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 59) 27 59 hvalid hfast

theorem sr27p60:∀ i ∈ List.range 1,StrictCheckAt 27 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 60) 27 60:=by decide +kernel
  have hfast:StrictAtFast (row 27 60) 27 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 60) 27 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 60) 27 60 hvalid hfast

theorem sr27p61:∀ i ∈ List.range 1,StrictCheckAt 27 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 61) 27 61:=by decide +kernel
  have hfast:StrictAtFast (row 27 61) 27 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 61) 27 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 61) 27 61 hvalid hfast

theorem sr27p62:∀ i ∈ List.range 1,StrictCheckAt 27 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 62) 27 62:=by decide +kernel
  have hfast:StrictAtFast (row 27 62) 27 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 62) 27 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 62) 27 62 hvalid hfast

theorem sr27p63:∀ i ∈ List.range 1,StrictCheckAt 27 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 63) 27 63:=by decide +kernel
  have hfast:StrictAtFast (row 27 63) 27 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 63) 27 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 63) 27 63 hvalid hfast

theorem sr27p64:∀ i ∈ List.range 1,StrictCheckAt 27 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 64) 27 64:=by decide +kernel
  have hfast:StrictAtFast (row 27 64) 27 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 64) 27 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 64) 27 64 hvalid hfast

theorem sr27p65:∀ i ∈ List.range 1,StrictCheckAt 27 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 65) 27 65:=by decide +kernel
  have hfast:StrictAtFast (row 27 65) 27 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 65) 27 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 65) 27 65 hvalid hfast

theorem sr27p66:∀ i ∈ List.range 1,StrictCheckAt 27 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 66) 27 66:=by decide +kernel
  have hfast:StrictAtFast (row 27 66) 27 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 66) 27 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 66) 27 66 hvalid hfast

theorem sr27p67:∀ i ∈ List.range 1,StrictCheckAt 27 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 67) 27 67:=by decide +kernel
  have hfast:StrictAtFast (row 27 67) 27 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 67) 27 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 67) 27 67 hvalid hfast

theorem sr27p68:∀ i ∈ List.range 1,StrictCheckAt 27 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 68) 27 68:=by decide +kernel
  have hfast:StrictAtFast (row 27 68) 27 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 68) 27 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 68) 27 68 hvalid hfast

theorem sr27p69:∀ i ∈ List.range 1,StrictCheckAt 27 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 69) 27 69:=by decide +kernel
  have hfast:StrictAtFast (row 27 69) 27 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 69) 27 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 69) 27 69 hvalid hfast

theorem sr27p70:∀ i ∈ List.range 1,StrictCheckAt 27 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 70) 27 70:=by decide +kernel
  have hfast:StrictAtFast (row 27 70) 27 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 70) 27 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 70) 27 70 hvalid hfast

theorem sr27p71:∀ i ∈ List.range 1,StrictCheckAt 27 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 71) 27 71:=by decide +kernel
  have hfast:StrictAtFast (row 27 71) 27 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 71) 27 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 71) 27 71 hvalid hfast

theorem sr27p72:∀ i ∈ List.range 1,StrictCheckAt 27 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 72) 27 72:=by decide +kernel
  have hfast:StrictAtFast (row 27 72) 27 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 72) 27 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 72) 27 72 hvalid hfast

theorem sr27p73:∀ i ∈ List.range 1,StrictCheckAt 27 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 73) 27 73:=by decide +kernel
  have hfast:StrictAtFast (row 27 73) 27 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 73) 27 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 73) 27 73 hvalid hfast

theorem sr27p74:∀ i ∈ List.range 1,StrictCheckAt 27 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 74) 27 74:=by decide +kernel
  have hfast:StrictAtFast (row 27 74) 27 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 74) 27 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 74) 27 74 hvalid hfast

theorem sr27p75:∀ i ∈ List.range 1,StrictCheckAt 27 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 75) 27 75:=by decide +kernel
  have hfast:StrictAtFast (row 27 75) 27 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 75) 27 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 75) 27 75 hvalid hfast

theorem sr27p76:∀ i ∈ List.range 1,StrictCheckAt 27 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 76) 27 76:=by decide +kernel
  have hfast:StrictAtFast (row 27 76) 27 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 76) 27 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 76) 27 76 hvalid hfast

theorem sr27p77:∀ i ∈ List.range 1,StrictCheckAt 27 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 77) 27 77:=by decide +kernel
  have hfast:StrictAtFast (row 27 77) 27 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 77) 27 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 77) 27 77 hvalid hfast

theorem sr27p78:∀ i ∈ List.range 1,StrictCheckAt 27 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 78) 27 78:=by decide +kernel
  have hfast:StrictAtFast (row 27 78) 27 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 78) 27 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 78) 27 78 hvalid hfast

theorem sr27p79:∀ i ∈ List.range 1,StrictCheckAt 27 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 79) 27 79:=by decide +kernel
  have hfast:StrictAtFast (row 27 79) 27 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 79) 27 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 79) 27 79 hvalid hfast

theorem sr27p80:∀ i ∈ List.range 1,StrictCheckAt 27 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 80) 27 80:=by decide +kernel
  have hfast:StrictAtFast (row 27 80) 27 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 80) 27 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 80) 27 80 hvalid hfast

theorem sr27p81:∀ i ∈ List.range 1,StrictCheckAt 27 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 81) 27 81:=by decide +kernel
  have hfast:StrictAtFast (row 27 81) 27 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 81) 27 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 81) 27 81 hvalid hfast

theorem sr27p82:∀ i ∈ List.range 1,StrictCheckAt 27 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 82) 27 82:=by decide +kernel
  have hfast:StrictAtFast (row 27 82) 27 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 82) 27 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 82) 27 82 hvalid hfast

theorem sr27p83:∀ i ∈ List.range 1,StrictCheckAt 27 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 83) 27 83:=by decide +kernel
  have hfast:StrictAtFast (row 27 83) 27 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 83) 27 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 83) 27 83 hvalid hfast

theorem sr27p84:∀ i ∈ List.range 1,StrictCheckAt 27 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 84) 27 84:=by decide +kernel
  have hfast:StrictAtFast (row 27 84) 27 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 84) 27 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 84) 27 84 hvalid hfast

theorem sr27p85:∀ i ∈ List.range 1,StrictCheckAt 27 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 85) 27 85:=by decide +kernel
  have hfast:StrictAtFast (row 27 85) 27 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 85) 27 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 85) 27 85 hvalid hfast

theorem sr27p86:∀ i ∈ List.range 1,StrictCheckAt 27 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 86) 27 86:=by decide +kernel
  have hfast:StrictAtFast (row 27 86) 27 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 86) 27 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 86) 27 86 hvalid hfast

theorem sr27p87:∀ i ∈ List.range 1,StrictCheckAt 27 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 87) 27 87:=by decide +kernel
  have hfast:StrictAtFast (row 27 87) 27 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 87) 27 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 87) 27 87 hvalid hfast

theorem sr27p88:∀ i ∈ List.range 1,StrictCheckAt 27 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 88) 27 88:=by decide +kernel
  have hfast:StrictAtFast (row 27 88) 27 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 88) 27 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 88) 27 88 hvalid hfast

theorem sr27p89:∀ i ∈ List.range 1,StrictCheckAt 27 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 89) 27 89:=by decide +kernel
  have hfast:StrictAtFast (row 27 89) 27 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 89) 27 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 89) 27 89 hvalid hfast

theorem sr27p90:∀ i ∈ List.range 1,StrictCheckAt 27 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 90) 27 90:=by decide +kernel
  have hfast:StrictAtFast (row 27 90) 27 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 90) 27 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 90) 27 90 hvalid hfast

theorem sr27p91:∀ i ∈ List.range 1,StrictCheckAt 27 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 91) 27 91:=by decide +kernel
  have hfast:StrictAtFast (row 27 91) 27 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 91) 27 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 91) 27 91 hvalid hfast

theorem sr27p92:∀ i ∈ List.range 1,StrictCheckAt 27 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 92) 27 92:=by decide +kernel
  have hfast:StrictAtFast (row 27 92) 27 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 92) 27 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 92) 27 92 hvalid hfast

theorem sr27p93:∀ i ∈ List.range 1,StrictCheckAt 27 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 93) 27 93:=by decide +kernel
  have hfast:StrictAtFast (row 27 93) 27 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 93) 27 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 93) 27 93 hvalid hfast

theorem sr27p94:∀ i ∈ List.range 1,StrictCheckAt 27 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 94) 27 94:=by decide +kernel
  have hfast:StrictAtFast (row 27 94) 27 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 94) 27 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 94) 27 94 hvalid hfast

theorem sr27p95:∀ i ∈ List.range 1,StrictCheckAt 27 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 95) 27 95:=by decide +kernel
  have hfast:StrictAtFast (row 27 95) 27 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 95) 27 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 95) 27 95 hvalid hfast

theorem sr27p96:∀ i ∈ List.range 1,StrictCheckAt 27 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 96) 27 96:=by decide +kernel
  have hfast:StrictAtFast (row 27 96) 27 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 96) 27 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 96) 27 96 hvalid hfast

theorem sr27p97:∀ i ∈ List.range 1,StrictCheckAt 27 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 97) 27 97:=by decide +kernel
  have hfast:StrictAtFast (row 27 97) 27 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 97) 27 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 97) 27 97 hvalid hfast

theorem sr27p98:∀ i ∈ List.range 1,StrictCheckAt 27 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 98) 27 98:=by decide +kernel
  have hfast:StrictAtFast (row 27 98) 27 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 98) 27 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 98) 27 98 hvalid hfast

theorem sr27p99:∀ i ∈ List.range 1,StrictCheckAt 27 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 99) 27 99:=by decide +kernel
  have hfast:StrictAtFast (row 27 99) 27 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 99) 27 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 99) 27 99 hvalid hfast

theorem sr27p100:∀ i ∈ List.range 1,StrictCheckAt 27 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 100) 27 100:=by decide +kernel
  have hfast:StrictAtFast (row 27 100) 27 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 100) 27 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 100) 27 100 hvalid hfast

theorem sr27p101:∀ i ∈ List.range 1,StrictCheckAt 27 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 101) 27 101:=by decide +kernel
  have hfast:StrictAtFast (row 27 101) 27 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 101) 27 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 101) 27 101 hvalid hfast

theorem sr27p102:∀ i ∈ List.range 1,StrictCheckAt 27 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 102) 27 102:=by decide +kernel
  have hfast:StrictAtFast (row 27 102) 27 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 102) 27 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 102) 27 102 hvalid hfast

theorem sr27p103:∀ i ∈ List.range 1,StrictCheckAt 27 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 103) 27 103:=by decide +kernel
  have hfast:StrictAtFast (row 27 103) 27 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 103) 27 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 103) 27 103 hvalid hfast

theorem sr27p104:∀ i ∈ List.range 1,StrictCheckAt 27 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 104) 27 104:=by decide +kernel
  have hfast:StrictAtFast (row 27 104) 27 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 104) 27 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 104) 27 104 hvalid hfast

theorem sr27p105:∀ i ∈ List.range 1,StrictCheckAt 27 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 105) 27 105:=by decide +kernel
  have hfast:StrictAtFast (row 27 105) 27 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 105) 27 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 105) 27 105 hvalid hfast

theorem sr27p106:∀ i ∈ List.range 1,StrictCheckAt 27 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 106) 27 106:=by decide +kernel
  have hfast:StrictAtFast (row 27 106) 27 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 106) 27 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 106) 27 106 hvalid hfast

theorem sr27p107:∀ i ∈ List.range 1,StrictCheckAt 27 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 107) 27 107:=by decide +kernel
  have hfast:StrictAtFast (row 27 107) 27 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 107) 27 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 107) 27 107 hvalid hfast

theorem sr27p108:∀ i ∈ List.range 1,StrictCheckAt 27 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 108) 27 108:=by decide +kernel
  have hfast:StrictAtFast (row 27 108) 27 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 108) 27 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 108) 27 108 hvalid hfast

theorem sr27p109:∀ i ∈ List.range 1,StrictCheckAt 27 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 109) 27 109:=by decide +kernel
  have hfast:StrictAtFast (row 27 109) 27 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 109) 27 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 109) 27 109 hvalid hfast

theorem sr27p110:∀ i ∈ List.range 1,StrictCheckAt 27 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 110) 27 110:=by decide +kernel
  have hfast:StrictAtFast (row 27 110) 27 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 110) 27 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 110) 27 110 hvalid hfast

theorem sr27p111:∀ i ∈ List.range 1,StrictCheckAt 27 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 111) 27 111:=by decide +kernel
  have hfast:StrictAtFast (row 27 111) 27 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 111) 27 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 111) 27 111 hvalid hfast

theorem sr27p112:∀ i ∈ List.range 1,StrictCheckAt 27 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 112) 27 112:=by decide +kernel
  have hfast:StrictAtFast (row 27 112) 27 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 112) 27 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 112) 27 112 hvalid hfast

theorem sr27p113:∀ i ∈ List.range 1,StrictCheckAt 27 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 113) 27 113:=by decide +kernel
  have hfast:StrictAtFast (row 27 113) 27 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 113) 27 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 113) 27 113 hvalid hfast

theorem sr27p114:∀ i ∈ List.range 1,StrictCheckAt 27 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 114) 27 114:=by decide +kernel
  have hfast:StrictAtFast (row 27 114) 27 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 114) 27 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 114) 27 114 hvalid hfast

theorem sr27p115:∀ i ∈ List.range 1,StrictCheckAt 27 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 27 115) 27 115:=by decide +kernel
  have hfast:StrictAtFast (row 27 115) 27 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 27 115) 27 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 27 115) 27 115 hvalid hfast

theorem br27p0:∀ i ∈ List.range 4,BaseCheckAt 27 (0+i):=by decide +kernel

theorem br27p1:∀ i ∈ List.range 4,BaseCheckAt 27 (4+i):=by decide +kernel

theorem br27p2:∀ i ∈ List.range 4,BaseCheckAt 27 (8+i):=by decide +kernel

theorem br27p3:∀ i ∈ List.range 4,BaseCheckAt 27 (12+i):=by decide +kernel

theorem br27p4:∀ i ∈ List.range 4,BaseCheckAt 27 (16+i):=by decide +kernel

theorem br27p5:∀ i ∈ List.range 4,BaseCheckAt 27 (20+i):=by decide +kernel

theorem br27p6:∀ i ∈ List.range 4,BaseCheckAt 27 (24+i):=by decide +kernel

theorem br27p7:∀ i ∈ List.range 4,BaseCheckAt 27 (28+i):=by decide +kernel

theorem br27p8:∀ i ∈ List.range 4,BaseCheckAt 27 (32+i):=by decide +kernel

theorem br27p9:∀ i ∈ List.range 4,BaseCheckAt 27 (36+i):=by decide +kernel

theorem br27p10:∀ i ∈ List.range 4,BaseCheckAt 27 (40+i):=by decide +kernel

theorem br27p11:∀ i ∈ List.range 4,BaseCheckAt 27 (44+i):=by decide +kernel

theorem br27p12:∀ i ∈ List.range 4,BaseCheckAt 27 (48+i):=by decide +kernel

theorem br27p13:∀ i ∈ List.range 4,BaseCheckAt 27 (52+i):=by decide +kernel

theorem br27p14:∀ i ∈ List.range 4,BaseCheckAt 27 (56+i):=by decide +kernel

theorem br27p15:∀ i ∈ List.range 4,BaseCheckAt 27 (60+i):=by decide +kernel



theorem br27p16:∀ i ∈ List.range 4,BaseCheckAt 27 (64+i):=by decide +kernel

theorem br27p17:∀ i ∈ List.range 4,BaseCheckAt 27 (68+i):=by decide +kernel

theorem br27p18:∀ i ∈ List.range 4,BaseCheckAt 27 (72+i):=by decide +kernel

theorem br27p19:∀ i ∈ List.range 4,BaseCheckAt 27 (76+i):=by decide +kernel

theorem br27p20:∀ i ∈ List.range 4,BaseCheckAt 27 (80+i):=by decide +kernel

theorem br27p21:∀ i ∈ List.range 4,BaseCheckAt 27 (84+i):=by decide +kernel

theorem br27p22:∀ i ∈ List.range 4,BaseCheckAt 27 (88+i):=by decide +kernel

theorem br27p23:∀ i ∈ List.range 4,BaseCheckAt 27 (92+i):=by decide +kernel

theorem br27p24:∀ i ∈ List.range 4,BaseCheckAt 27 (96+i):=by decide +kernel

theorem br27p25:∀ i ∈ List.range 4,BaseCheckAt 27 (100+i):=by decide +kernel

theorem br27p26:∀ i ∈ List.range 4,BaseCheckAt 27 (104+i):=by decide +kernel

theorem br27p27:∀ i ∈ List.range 4,BaseCheckAt 27 (108+i):=by decide +kernel

theorem br27p28:∀ i ∈ List.range 4,BaseCheckAt 27 (112+i):=by decide +kernel



theorem cr27:∀ V ∈ List.range 116,CorrectAt 27 V:=by
  intro V hV
  have hv:V < 116:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr27p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr27p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr27p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr27p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr27p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr27p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr27p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr27p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr27p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr27p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr27p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr27p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr27p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr27p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr27p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr27:∀ V ∈ List.range 116,ZeroCheckAt 27 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 27 V (by omega) (by omega) (by omega)
theorem sr27:∀ V ∈ List.range 116,StrictCheckAt 27 V:=by
  intro V hV
  have hv:V < 116:=List.mem_range.mp hV
  by_cases h0_116:V < 58
  · by_cases h0_58:V < 29
    · by_cases h0_29:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr27p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr27p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr27p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr27p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr27p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr27p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr27p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr27p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr27p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr27p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr27p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr27p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr27p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr27p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_29:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr27p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr27p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr27p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr27p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr27p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr27p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr27p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_29:V < 25
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have h:=sr27p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr27p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
            · by_cases h23_25:V < 24
              · have h:=sr27p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr27p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have h:=sr27p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr27p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
            · by_cases h27_29:V < 28
              · have h:=sr27p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr27p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h29_58:V < 43
      · by_cases h29_43:V < 36
        · by_cases h29_36:V < 32
          · by_cases h29_32:V < 30
            · have h:=sr27p29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_32:V < 31
              · have h:=sr27p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · have h:=sr27p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have h:=sr27p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr27p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
            · by_cases h34_36:V < 35
              · have h:=sr27p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr27p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
        · by_cases h36_43:V < 39
          · by_cases h36_39:V < 37
            · have h:=sr27p36 (V-36) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
            · by_cases h37_39:V < 38
              · have h:=sr27p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr27p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
          · by_cases h39_43:V < 41
            · by_cases h39_41:V < 40
              · have h:=sr27p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr27p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
            · by_cases h41_43:V < 42
              · have h:=sr27p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr27p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
      · by_cases h43_58:V < 50
        · by_cases h43_50:V < 46
          · by_cases h43_46:V < 44
            · have h:=sr27p43 (V-43) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
            · by_cases h44_46:V < 45
              · have h:=sr27p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
              · have h:=sr27p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
          · by_cases h46_50:V < 48
            · by_cases h46_48:V < 47
              · have h:=sr27p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
              · have h:=sr27p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
            · by_cases h48_50:V < 49
              · have h:=sr27p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
              · have h:=sr27p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
        · by_cases h50_58:V < 54
          · by_cases h50_54:V < 52
            · by_cases h50_52:V < 51
              · have h:=sr27p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr27p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
            · by_cases h52_54:V < 53
              · have h:=sr27p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr27p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
          · by_cases h54_58:V < 56
            · by_cases h54_56:V < 55
              · have h:=sr27p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr27p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
            · by_cases h56_58:V < 57
              · have h:=sr27p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
              · have h:=sr27p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
  · by_cases h58_116:V < 87
    · by_cases h58_87:V < 72
      · by_cases h58_72:V < 65
        · by_cases h58_65:V < 61
          · by_cases h58_61:V < 59
            · have h:=sr27p58 (V-58) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
            · by_cases h59_61:V < 60
              · have h:=sr27p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr27p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · by_cases h61_65:V < 63
            · by_cases h61_63:V < 62
              · have h:=sr27p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr27p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
            · by_cases h63_65:V < 64
              · have h:=sr27p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · have h:=sr27p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · by_cases h65_72:V < 68
          · by_cases h65_68:V < 66
            · have h:=sr27p65 (V-65) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
            · by_cases h66_68:V < 67
              · have h:=sr27p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr27p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
          · by_cases h68_72:V < 70
            · by_cases h68_70:V < 69
              · have h:=sr27p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr27p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
            · by_cases h70_72:V < 71
              · have h:=sr27p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr27p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
      · by_cases h72_87:V < 79
        · by_cases h72_79:V < 75
          · by_cases h72_75:V < 73
            · have h:=sr27p72 (V-72) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
            · by_cases h73_75:V < 74
              · have h:=sr27p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr27p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
          · by_cases h75_79:V < 77
            · by_cases h75_77:V < 76
              · have h:=sr27p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr27p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
            · by_cases h77_79:V < 78
              · have h:=sr27p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr27p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
        · by_cases h79_87:V < 83
          · by_cases h79_83:V < 81
            · by_cases h79_81:V < 80
              · have h:=sr27p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr27p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
            · by_cases h81_83:V < 82
              · have h:=sr27p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr27p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
          · by_cases h83_87:V < 85
            · by_cases h83_85:V < 84
              · have h:=sr27p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr27p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
            · by_cases h85_87:V < 86
              · have h:=sr27p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr27p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
    · by_cases h87_116:V < 101
      · by_cases h87_101:V < 94
        · by_cases h87_94:V < 90
          · by_cases h87_90:V < 88
            · have h:=sr27p87 (V-87) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
            · by_cases h88_90:V < 89
              · have h:=sr27p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr27p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have h:=sr27p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr27p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr27p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr27p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
        · by_cases h94_101:V < 97
          · by_cases h94_97:V < 95
            · have h:=sr27p94 (V-94) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
            · by_cases h95_97:V < 96
              · have h:=sr27p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr27p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · by_cases h97_101:V < 99
            · by_cases h97_99:V < 98
              · have h:=sr27p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr27p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_101:V < 100
              · have h:=sr27p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr27p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
      · by_cases h101_116:V < 108
        · by_cases h101_108:V < 104
          · by_cases h101_104:V < 102
            · have h:=sr27p101 (V-101) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
            · by_cases h102_104:V < 103
              · have h:=sr27p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr27p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
          · by_cases h104_108:V < 106
            · by_cases h104_106:V < 105
              · have h:=sr27p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr27p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
            · by_cases h106_108:V < 107
              · have h:=sr27p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr27p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
        · by_cases h108_116:V < 112
          · by_cases h108_112:V < 110
            · by_cases h108_110:V < 109
              · have h:=sr27p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr27p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
            · by_cases h110_112:V < 111
              · have h:=sr27p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr27p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
          · by_cases h112_116:V < 114
            · by_cases h112_114:V < 113
              · have h:=sr27p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr27p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
            · by_cases h114_116:V < 115
              · have h:=sr27p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
              · have h:=sr27p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h

theorem br27:∀ V ∈ List.range 116,BaseCheckAt 27 V:=by
  intro V hV
  have hv:V < 116:=List.mem_range.mp hV
  by_cases h0_29:V < 56
  · by_cases h0_14:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br27p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br27p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br27p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br27p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br27p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br27p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br27p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_14:V < 40
      · by_cases h7_10:V < 32
        · have h:=br27p7 (V-28) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
        · by_cases h8_10:V < 36
          · have h:=br27p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br27p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
      · by_cases h10_14:V < 48
        · by_cases h10_12:V < 44
          · have h:=br27p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br27p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
        · by_cases h12_14:V < 52
          · have h:=br27p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br27p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
  · by_cases h14_29:V < 84
    · by_cases h14_21:V < 68
      · by_cases h14_17:V < 60
        · have h:=br27p14 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · by_cases h15_17:V < 64
          · have h:=br27p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br27p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br27p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br27p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br27p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br27p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h21_29:V < 100
      · by_cases h21_25:V < 92
        · by_cases h21_23:V < 88
          · have h:=br27p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br27p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h23_25:V < 96
          · have h:=br27p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br27p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h25_29:V < 108
        · by_cases h25_27:V < 104
          · have h:=br27p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br27p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h27_29:V < 112
          · have h:=br27p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br27p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
