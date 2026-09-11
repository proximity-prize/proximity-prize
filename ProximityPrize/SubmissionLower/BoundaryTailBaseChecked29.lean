import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr29p0:∀ i ∈ List.range 8,CorrectAt 29 (0+i):=by decide +kernel

theorem cr29p1:∀ i ∈ List.range 8,CorrectAt 29 (8+i):=by decide +kernel

theorem cr29p2:∀ i ∈ List.range 8,CorrectAt 29 (16+i):=by decide +kernel

theorem cr29p3:∀ i ∈ List.range 8,CorrectAt 29 (24+i):=by decide +kernel

theorem cr29p4:∀ i ∈ List.range 8,CorrectAt 29 (32+i):=by decide +kernel

theorem cr29p5:∀ i ∈ List.range 8,CorrectAt 29 (40+i):=by decide +kernel

theorem cr29p6:∀ i ∈ List.range 8,CorrectAt 29 (48+i):=by decide +kernel

theorem cr29p7:∀ i ∈ List.range 8,CorrectAt 29 (56+i):=by decide +kernel

theorem cr29p8:∀ i ∈ List.range 8,CorrectAt 29 (64+i):=by decide +kernel

theorem cr29p9:∀ i ∈ List.range 8,CorrectAt 29 (72+i):=by decide +kernel

theorem cr29p10:∀ i ∈ List.range 8,CorrectAt 29 (80+i):=by decide +kernel

theorem cr29p11:∀ i ∈ List.range 8,CorrectAt 29 (88+i):=by decide +kernel

theorem cr29p12:∀ i ∈ List.range 8,CorrectAt 29 (96+i):=by decide +kernel

theorem cr29p13:∀ i ∈ List.range 8,CorrectAt 29 (104+i):=by decide +kernel

theorem cr29p14:∀ i ∈ List.range 2,CorrectAt 29 (112+i):=by decide +kernel

theorem sr29p0:∀ i ∈ List.range 1,StrictCheckAt 29 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 0) 29 0:=by decide +kernel
  have hfast:StrictAtFast (row 29 0) 29 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 0) 29 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 0) 29 0 hvalid hfast

theorem sr29p1:∀ i ∈ List.range 1,StrictCheckAt 29 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 1) 29 1:=by decide +kernel
  have hfast:StrictAtFast (row 29 1) 29 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 1) 29 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 1) 29 1 hvalid hfast

theorem sr29p2:∀ i ∈ List.range 1,StrictCheckAt 29 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 2) 29 2:=by decide +kernel
  have hfast:StrictAtFast (row 29 2) 29 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 2) 29 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 2) 29 2 hvalid hfast

theorem sr29p3:∀ i ∈ List.range 1,StrictCheckAt 29 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 3) 29 3:=by decide +kernel
  have hfast:StrictAtFast (row 29 3) 29 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 3) 29 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 3) 29 3 hvalid hfast

theorem sr29p4:∀ i ∈ List.range 1,StrictCheckAt 29 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 4) 29 4:=by decide +kernel
  have hfast:StrictAtFast (row 29 4) 29 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 4) 29 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 4) 29 4 hvalid hfast

theorem sr29p5:∀ i ∈ List.range 1,StrictCheckAt 29 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 5) 29 5:=by decide +kernel
  have hfast:StrictAtFast (row 29 5) 29 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 5) 29 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 5) 29 5 hvalid hfast

theorem sr29p6:∀ i ∈ List.range 1,StrictCheckAt 29 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 6) 29 6:=by decide +kernel
  have hfast:StrictAtFast (row 29 6) 29 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 6) 29 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 6) 29 6 hvalid hfast

theorem sr29p7:∀ i ∈ List.range 1,StrictCheckAt 29 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 7) 29 7:=by decide +kernel
  have hfast:StrictAtFast (row 29 7) 29 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 7) 29 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 7) 29 7 hvalid hfast

theorem sr29p8:∀ i ∈ List.range 1,StrictCheckAt 29 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 8) 29 8:=by decide +kernel
  have hfast:StrictAtFast (row 29 8) 29 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 8) 29 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 8) 29 8 hvalid hfast

theorem sr29p9:∀ i ∈ List.range 1,StrictCheckAt 29 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 9) 29 9:=by decide +kernel
  have hfast:StrictAtFast (row 29 9) 29 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 9) 29 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 9) 29 9 hvalid hfast

theorem sr29p10:∀ i ∈ List.range 1,StrictCheckAt 29 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 10) 29 10:=by decide +kernel
  have hfast:StrictAtFast (row 29 10) 29 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 10) 29 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 10) 29 10 hvalid hfast

theorem sr29p11:∀ i ∈ List.range 1,StrictCheckAt 29 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 11) 29 11:=by decide +kernel
  have hfast:StrictAtFast (row 29 11) 29 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 11) 29 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 11) 29 11 hvalid hfast

theorem sr29p12:∀ i ∈ List.range 1,StrictCheckAt 29 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 12) 29 12:=by decide +kernel
  have hfast:StrictAtFast (row 29 12) 29 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 12) 29 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 12) 29 12 hvalid hfast

theorem sr29p13:∀ i ∈ List.range 1,StrictCheckAt 29 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 13) 29 13:=by decide +kernel
  have hfast:StrictAtFast (row 29 13) 29 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 13) 29 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 13) 29 13 hvalid hfast

theorem sr29p14:∀ i ∈ List.range 1,StrictCheckAt 29 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 14) 29 14:=by decide +kernel
  have hfast:StrictAtFast (row 29 14) 29 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 14) 29 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 14) 29 14 hvalid hfast

theorem sr29p15:∀ i ∈ List.range 1,StrictCheckAt 29 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 15) 29 15:=by decide +kernel
  have hfast:StrictAtFast (row 29 15) 29 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 15) 29 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 15) 29 15 hvalid hfast

theorem sr29p16:∀ i ∈ List.range 1,StrictCheckAt 29 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 16) 29 16:=by decide +kernel
  have hfast:StrictAtFast (row 29 16) 29 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 16) 29 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 16) 29 16 hvalid hfast

theorem sr29p17:∀ i ∈ List.range 1,StrictCheckAt 29 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 17) 29 17:=by decide +kernel
  have hfast:StrictAtFast (row 29 17) 29 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 17) 29 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 17) 29 17 hvalid hfast

theorem sr29p18:∀ i ∈ List.range 1,StrictCheckAt 29 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 18) 29 18:=by decide +kernel
  have hfast:StrictAtFast (row 29 18) 29 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 18) 29 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 18) 29 18 hvalid hfast

theorem sr29p19:∀ i ∈ List.range 1,StrictCheckAt 29 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 19) 29 19:=by decide +kernel
  have hfast:StrictAtFast (row 29 19) 29 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 19) 29 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 19) 29 19 hvalid hfast

theorem sr29p20:∀ i ∈ List.range 1,StrictCheckAt 29 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 20) 29 20:=by decide +kernel
  have hfast:StrictAtFast (row 29 20) 29 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 20) 29 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 20) 29 20 hvalid hfast

theorem sr29p21:∀ i ∈ List.range 1,StrictCheckAt 29 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 21) 29 21:=by decide +kernel
  have hfast:StrictAtFast (row 29 21) 29 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 21) 29 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 21) 29 21 hvalid hfast

theorem sr29p22:∀ i ∈ List.range 1,StrictCheckAt 29 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 22) 29 22:=by decide +kernel
  have hfast:StrictAtFast (row 29 22) 29 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 22) 29 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 22) 29 22 hvalid hfast

theorem sr29p23:∀ i ∈ List.range 1,StrictCheckAt 29 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 23) 29 23:=by decide +kernel
  have hfast:StrictAtFast (row 29 23) 29 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 23) 29 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 23) 29 23 hvalid hfast

theorem sr29p24:∀ i ∈ List.range 1,StrictCheckAt 29 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 24) 29 24:=by decide +kernel
  have hfast:StrictAtFast (row 29 24) 29 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 24) 29 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 24) 29 24 hvalid hfast

theorem sr29p25:∀ i ∈ List.range 1,StrictCheckAt 29 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 25) 29 25:=by decide +kernel
  have hfast:StrictAtFast (row 29 25) 29 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 25) 29 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 25) 29 25 hvalid hfast

theorem sr29p26:∀ i ∈ List.range 1,StrictCheckAt 29 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 26) 29 26:=by decide +kernel
  have hfast:StrictAtFast (row 29 26) 29 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 26) 29 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 26) 29 26 hvalid hfast

theorem sr29p27:∀ i ∈ List.range 1,StrictCheckAt 29 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 27) 29 27:=by decide +kernel
  have hfast:StrictAtFast (row 29 27) 29 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 27) 29 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 27) 29 27 hvalid hfast

theorem sr29p28:∀ i ∈ List.range 1,StrictCheckAt 29 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 28) 29 28:=by decide +kernel
  have hfast:StrictAtFast (row 29 28) 29 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 28) 29 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 28) 29 28 hvalid hfast

theorem sr29p29:∀ i ∈ List.range 1,StrictCheckAt 29 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 29) 29 29:=by decide +kernel
  have hfast:StrictAtFast (row 29 29) 29 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 29) 29 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 29) 29 29 hvalid hfast

theorem sr29p30:∀ i ∈ List.range 1,StrictCheckAt 29 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 30) 29 30:=by decide +kernel
  have hfast:StrictAtFast (row 29 30) 29 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 30) 29 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 30) 29 30 hvalid hfast

theorem sr29p31:∀ i ∈ List.range 1,StrictCheckAt 29 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 31) 29 31:=by decide +kernel
  have hfast:StrictAtFast (row 29 31) 29 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 31) 29 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 31) 29 31 hvalid hfast

theorem sr29p32:∀ i ∈ List.range 1,StrictCheckAt 29 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 32) 29 32:=by decide +kernel
  have hfast:StrictAtFast (row 29 32) 29 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 32) 29 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 32) 29 32 hvalid hfast

theorem sr29p33:∀ i ∈ List.range 1,StrictCheckAt 29 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 33) 29 33:=by decide +kernel
  have hfast:StrictAtFast (row 29 33) 29 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 33) 29 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 33) 29 33 hvalid hfast

theorem sr29p34:∀ i ∈ List.range 1,StrictCheckAt 29 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 34) 29 34:=by decide +kernel
  have hfast:StrictAtFast (row 29 34) 29 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 34) 29 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 34) 29 34 hvalid hfast

theorem sr29p35:∀ i ∈ List.range 1,StrictCheckAt 29 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 35) 29 35:=by decide +kernel
  have hfast:StrictAtFast (row 29 35) 29 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 35) 29 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 35) 29 35 hvalid hfast

theorem sr29p36:∀ i ∈ List.range 1,StrictCheckAt 29 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 36) 29 36:=by decide +kernel
  have hfast:StrictAtFast (row 29 36) 29 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 36) 29 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 36) 29 36 hvalid hfast

theorem sr29p37:∀ i ∈ List.range 1,StrictCheckAt 29 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 37) 29 37:=by decide +kernel
  have hfast:StrictAtFast (row 29 37) 29 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 37) 29 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 37) 29 37 hvalid hfast

theorem sr29p38:∀ i ∈ List.range 1,StrictCheckAt 29 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 38) 29 38:=by decide +kernel
  have hfast:StrictAtFast (row 29 38) 29 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 38) 29 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 38) 29 38 hvalid hfast

theorem sr29p39:∀ i ∈ List.range 1,StrictCheckAt 29 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 39) 29 39:=by decide +kernel
  have hfast:StrictAtFast (row 29 39) 29 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 39) 29 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 39) 29 39 hvalid hfast

theorem sr29p40:∀ i ∈ List.range 1,StrictCheckAt 29 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 40) 29 40:=by decide +kernel
  have hfast:StrictAtFast (row 29 40) 29 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 40) 29 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 40) 29 40 hvalid hfast

theorem sr29p41:∀ i ∈ List.range 1,StrictCheckAt 29 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 41) 29 41:=by decide +kernel
  have hfast:StrictAtFast (row 29 41) 29 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 41) 29 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 41) 29 41 hvalid hfast

theorem sr29p42:∀ i ∈ List.range 1,StrictCheckAt 29 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 42) 29 42:=by decide +kernel
  have hfast:StrictAtFast (row 29 42) 29 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 42) 29 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 42) 29 42 hvalid hfast

theorem sr29p43:∀ i ∈ List.range 1,StrictCheckAt 29 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 43) 29 43:=by decide +kernel
  have hfast:StrictAtFast (row 29 43) 29 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 43) 29 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 43) 29 43 hvalid hfast

theorem sr29p44:∀ i ∈ List.range 1,StrictCheckAt 29 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 44) 29 44:=by decide +kernel
  have hfast:StrictAtFast (row 29 44) 29 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 44) 29 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 44) 29 44 hvalid hfast

theorem sr29p45:∀ i ∈ List.range 1,StrictCheckAt 29 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 45) 29 45:=by decide +kernel
  have hfast:StrictAtFast (row 29 45) 29 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 45) 29 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 45) 29 45 hvalid hfast

theorem sr29p46:∀ i ∈ List.range 1,StrictCheckAt 29 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 46) 29 46:=by decide +kernel
  have hfast:StrictAtFast (row 29 46) 29 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 46) 29 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 46) 29 46 hvalid hfast

theorem sr29p47:∀ i ∈ List.range 1,StrictCheckAt 29 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 47) 29 47:=by decide +kernel
  have hfast:StrictAtFast (row 29 47) 29 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 47) 29 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 47) 29 47 hvalid hfast

theorem sr29p48:∀ i ∈ List.range 1,StrictCheckAt 29 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 48) 29 48:=by decide +kernel
  have hfast:StrictAtFast (row 29 48) 29 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 48) 29 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 48) 29 48 hvalid hfast

theorem sr29p49:∀ i ∈ List.range 1,StrictCheckAt 29 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 49) 29 49:=by decide +kernel
  have hfast:StrictAtFast (row 29 49) 29 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 49) 29 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 49) 29 49 hvalid hfast

theorem sr29p50:∀ i ∈ List.range 1,StrictCheckAt 29 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 50) 29 50:=by decide +kernel
  have hfast:StrictAtFast (row 29 50) 29 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 50) 29 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 50) 29 50 hvalid hfast

theorem sr29p51:∀ i ∈ List.range 1,StrictCheckAt 29 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 51) 29 51:=by decide +kernel
  have hfast:StrictAtFast (row 29 51) 29 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 51) 29 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 51) 29 51 hvalid hfast

theorem sr29p52:∀ i ∈ List.range 1,StrictCheckAt 29 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 52) 29 52:=by decide +kernel
  have hfast:StrictAtFast (row 29 52) 29 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 52) 29 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 52) 29 52 hvalid hfast

theorem sr29p53:∀ i ∈ List.range 1,StrictCheckAt 29 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 53) 29 53:=by decide +kernel
  have hfast:StrictAtFast (row 29 53) 29 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 53) 29 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 53) 29 53 hvalid hfast

theorem sr29p54:∀ i ∈ List.range 1,StrictCheckAt 29 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 54) 29 54:=by decide +kernel
  have hfast:StrictAtFast (row 29 54) 29 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 54) 29 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 54) 29 54 hvalid hfast

theorem sr29p55:∀ i ∈ List.range 1,StrictCheckAt 29 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 55) 29 55:=by decide +kernel
  have hfast:StrictAtFast (row 29 55) 29 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 55) 29 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 55) 29 55 hvalid hfast

theorem sr29p56:∀ i ∈ List.range 1,StrictCheckAt 29 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 56) 29 56:=by decide +kernel
  have hfast:StrictAtFast (row 29 56) 29 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 56) 29 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 56) 29 56 hvalid hfast

theorem sr29p57:∀ i ∈ List.range 1,StrictCheckAt 29 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 57) 29 57:=by decide +kernel
  have hfast:StrictAtFast (row 29 57) 29 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 57) 29 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 57) 29 57 hvalid hfast

theorem sr29p58:∀ i ∈ List.range 1,StrictCheckAt 29 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 58) 29 58:=by decide +kernel
  have hfast:StrictAtFast (row 29 58) 29 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 58) 29 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 58) 29 58 hvalid hfast

theorem sr29p59:∀ i ∈ List.range 1,StrictCheckAt 29 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 59) 29 59:=by decide +kernel
  have hfast:StrictAtFast (row 29 59) 29 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 59) 29 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 59) 29 59 hvalid hfast

theorem sr29p60:∀ i ∈ List.range 1,StrictCheckAt 29 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 60) 29 60:=by decide +kernel
  have hfast:StrictAtFast (row 29 60) 29 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 60) 29 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 60) 29 60 hvalid hfast

theorem sr29p61:∀ i ∈ List.range 1,StrictCheckAt 29 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 61) 29 61:=by decide +kernel
  have hfast:StrictAtFast (row 29 61) 29 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 61) 29 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 61) 29 61 hvalid hfast

theorem sr29p62:∀ i ∈ List.range 1,StrictCheckAt 29 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 62) 29 62:=by decide +kernel
  have hfast:StrictAtFast (row 29 62) 29 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 62) 29 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 62) 29 62 hvalid hfast

theorem sr29p63:∀ i ∈ List.range 1,StrictCheckAt 29 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 63) 29 63:=by decide +kernel
  have hfast:StrictAtFast (row 29 63) 29 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 63) 29 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 63) 29 63 hvalid hfast

theorem sr29p64:∀ i ∈ List.range 1,StrictCheckAt 29 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 64) 29 64:=by decide +kernel
  have hfast:StrictAtFast (row 29 64) 29 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 64) 29 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 64) 29 64 hvalid hfast

theorem sr29p65:∀ i ∈ List.range 1,StrictCheckAt 29 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 65) 29 65:=by decide +kernel
  have hfast:StrictAtFast (row 29 65) 29 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 65) 29 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 65) 29 65 hvalid hfast

theorem sr29p66:∀ i ∈ List.range 1,StrictCheckAt 29 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 66) 29 66:=by decide +kernel
  have hfast:StrictAtFast (row 29 66) 29 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 66) 29 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 66) 29 66 hvalid hfast

theorem sr29p67:∀ i ∈ List.range 1,StrictCheckAt 29 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 67) 29 67:=by decide +kernel
  have hfast:StrictAtFast (row 29 67) 29 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 67) 29 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 67) 29 67 hvalid hfast

theorem sr29p68:∀ i ∈ List.range 1,StrictCheckAt 29 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 68) 29 68:=by decide +kernel
  have hfast:StrictAtFast (row 29 68) 29 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 68) 29 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 68) 29 68 hvalid hfast

theorem sr29p69:∀ i ∈ List.range 1,StrictCheckAt 29 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 69) 29 69:=by decide +kernel
  have hfast:StrictAtFast (row 29 69) 29 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 69) 29 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 69) 29 69 hvalid hfast

theorem sr29p70:∀ i ∈ List.range 1,StrictCheckAt 29 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 70) 29 70:=by decide +kernel
  have hfast:StrictAtFast (row 29 70) 29 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 70) 29 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 70) 29 70 hvalid hfast

theorem sr29p71:∀ i ∈ List.range 1,StrictCheckAt 29 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 71) 29 71:=by decide +kernel
  have hfast:StrictAtFast (row 29 71) 29 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 71) 29 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 71) 29 71 hvalid hfast

theorem sr29p72:∀ i ∈ List.range 1,StrictCheckAt 29 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 72) 29 72:=by decide +kernel
  have hfast:StrictAtFast (row 29 72) 29 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 72) 29 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 72) 29 72 hvalid hfast

theorem sr29p73:∀ i ∈ List.range 1,StrictCheckAt 29 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 73) 29 73:=by decide +kernel
  have hfast:StrictAtFast (row 29 73) 29 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 73) 29 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 73) 29 73 hvalid hfast

theorem sr29p74:∀ i ∈ List.range 1,StrictCheckAt 29 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 74) 29 74:=by decide +kernel
  have hfast:StrictAtFast (row 29 74) 29 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 74) 29 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 74) 29 74 hvalid hfast

theorem sr29p75:∀ i ∈ List.range 1,StrictCheckAt 29 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 75) 29 75:=by decide +kernel
  have hfast:StrictAtFast (row 29 75) 29 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 75) 29 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 75) 29 75 hvalid hfast

theorem sr29p76:∀ i ∈ List.range 1,StrictCheckAt 29 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 76) 29 76:=by decide +kernel
  have hfast:StrictAtFast (row 29 76) 29 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 76) 29 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 76) 29 76 hvalid hfast

theorem sr29p77:∀ i ∈ List.range 1,StrictCheckAt 29 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 77) 29 77:=by decide +kernel
  have hfast:StrictAtFast (row 29 77) 29 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 77) 29 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 77) 29 77 hvalid hfast

theorem sr29p78:∀ i ∈ List.range 1,StrictCheckAt 29 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 78) 29 78:=by decide +kernel
  have hfast:StrictAtFast (row 29 78) 29 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 78) 29 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 78) 29 78 hvalid hfast

theorem sr29p79:∀ i ∈ List.range 1,StrictCheckAt 29 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 79) 29 79:=by decide +kernel
  have hfast:StrictAtFast (row 29 79) 29 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 79) 29 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 79) 29 79 hvalid hfast

theorem sr29p80:∀ i ∈ List.range 1,StrictCheckAt 29 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 80) 29 80:=by decide +kernel
  have hfast:StrictAtFast (row 29 80) 29 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 80) 29 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 80) 29 80 hvalid hfast

theorem sr29p81:∀ i ∈ List.range 1,StrictCheckAt 29 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 81) 29 81:=by decide +kernel
  have hfast:StrictAtFast (row 29 81) 29 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 81) 29 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 81) 29 81 hvalid hfast

theorem sr29p82:∀ i ∈ List.range 1,StrictCheckAt 29 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 82) 29 82:=by decide +kernel
  have hfast:StrictAtFast (row 29 82) 29 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 82) 29 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 82) 29 82 hvalid hfast

theorem sr29p83:∀ i ∈ List.range 1,StrictCheckAt 29 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 83) 29 83:=by decide +kernel
  have hfast:StrictAtFast (row 29 83) 29 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 83) 29 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 83) 29 83 hvalid hfast

theorem sr29p84:∀ i ∈ List.range 1,StrictCheckAt 29 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 84) 29 84:=by decide +kernel
  have hfast:StrictAtFast (row 29 84) 29 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 84) 29 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 84) 29 84 hvalid hfast

theorem sr29p85:∀ i ∈ List.range 1,StrictCheckAt 29 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 85) 29 85:=by decide +kernel
  have hfast:StrictAtFast (row 29 85) 29 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 85) 29 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 85) 29 85 hvalid hfast

theorem sr29p86:∀ i ∈ List.range 1,StrictCheckAt 29 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 86) 29 86:=by decide +kernel
  have hfast:StrictAtFast (row 29 86) 29 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 86) 29 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 86) 29 86 hvalid hfast

theorem sr29p87:∀ i ∈ List.range 1,StrictCheckAt 29 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 87) 29 87:=by decide +kernel
  have hfast:StrictAtFast (row 29 87) 29 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 87) 29 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 87) 29 87 hvalid hfast

theorem sr29p88:∀ i ∈ List.range 1,StrictCheckAt 29 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 88) 29 88:=by decide +kernel
  have hfast:StrictAtFast (row 29 88) 29 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 88) 29 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 88) 29 88 hvalid hfast

theorem sr29p89:∀ i ∈ List.range 1,StrictCheckAt 29 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 89) 29 89:=by decide +kernel
  have hfast:StrictAtFast (row 29 89) 29 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 89) 29 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 89) 29 89 hvalid hfast

theorem sr29p90:∀ i ∈ List.range 1,StrictCheckAt 29 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 90) 29 90:=by decide +kernel
  have hfast:StrictAtFast (row 29 90) 29 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 90) 29 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 90) 29 90 hvalid hfast

theorem sr29p91:∀ i ∈ List.range 1,StrictCheckAt 29 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 91) 29 91:=by decide +kernel
  have hfast:StrictAtFast (row 29 91) 29 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 91) 29 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 91) 29 91 hvalid hfast

theorem sr29p92:∀ i ∈ List.range 1,StrictCheckAt 29 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 92) 29 92:=by decide +kernel
  have hfast:StrictAtFast (row 29 92) 29 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 92) 29 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 92) 29 92 hvalid hfast

theorem sr29p93:∀ i ∈ List.range 1,StrictCheckAt 29 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 93) 29 93:=by decide +kernel
  have hfast:StrictAtFast (row 29 93) 29 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 93) 29 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 93) 29 93 hvalid hfast

theorem sr29p94:∀ i ∈ List.range 1,StrictCheckAt 29 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 94) 29 94:=by decide +kernel
  have hfast:StrictAtFast (row 29 94) 29 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 94) 29 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 94) 29 94 hvalid hfast

theorem sr29p95:∀ i ∈ List.range 1,StrictCheckAt 29 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 95) 29 95:=by decide +kernel
  have hfast:StrictAtFast (row 29 95) 29 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 95) 29 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 95) 29 95 hvalid hfast

theorem sr29p96:∀ i ∈ List.range 1,StrictCheckAt 29 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 96) 29 96:=by decide +kernel
  have hfast:StrictAtFast (row 29 96) 29 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 96) 29 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 96) 29 96 hvalid hfast

theorem sr29p97:∀ i ∈ List.range 1,StrictCheckAt 29 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 97) 29 97:=by decide +kernel
  have hfast:StrictAtFast (row 29 97) 29 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 97) 29 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 97) 29 97 hvalid hfast

theorem sr29p98:∀ i ∈ List.range 1,StrictCheckAt 29 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 98) 29 98:=by decide +kernel
  have hfast:StrictAtFast (row 29 98) 29 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 98) 29 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 98) 29 98 hvalid hfast

theorem sr29p99:∀ i ∈ List.range 1,StrictCheckAt 29 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 99) 29 99:=by decide +kernel
  have hfast:StrictAtFast (row 29 99) 29 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 99) 29 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 99) 29 99 hvalid hfast

theorem sr29p100:∀ i ∈ List.range 1,StrictCheckAt 29 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 100) 29 100:=by decide +kernel
  have hfast:StrictAtFast (row 29 100) 29 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 100) 29 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 100) 29 100 hvalid hfast

theorem sr29p101:∀ i ∈ List.range 1,StrictCheckAt 29 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 101) 29 101:=by decide +kernel
  have hfast:StrictAtFast (row 29 101) 29 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 101) 29 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 101) 29 101 hvalid hfast

theorem sr29p102:∀ i ∈ List.range 1,StrictCheckAt 29 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 102) 29 102:=by decide +kernel
  have hfast:StrictAtFast (row 29 102) 29 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 102) 29 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 102) 29 102 hvalid hfast

theorem sr29p103:∀ i ∈ List.range 1,StrictCheckAt 29 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 103) 29 103:=by decide +kernel
  have hfast:StrictAtFast (row 29 103) 29 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 103) 29 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 103) 29 103 hvalid hfast

theorem sr29p104:∀ i ∈ List.range 1,StrictCheckAt 29 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 104) 29 104:=by decide +kernel
  have hfast:StrictAtFast (row 29 104) 29 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 104) 29 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 104) 29 104 hvalid hfast

theorem sr29p105:∀ i ∈ List.range 1,StrictCheckAt 29 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 105) 29 105:=by decide +kernel
  have hfast:StrictAtFast (row 29 105) 29 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 105) 29 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 105) 29 105 hvalid hfast

theorem sr29p106:∀ i ∈ List.range 1,StrictCheckAt 29 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 106) 29 106:=by decide +kernel
  have hfast:StrictAtFast (row 29 106) 29 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 106) 29 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 106) 29 106 hvalid hfast

theorem sr29p107:∀ i ∈ List.range 1,StrictCheckAt 29 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 107) 29 107:=by decide +kernel
  have hfast:StrictAtFast (row 29 107) 29 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 107) 29 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 107) 29 107 hvalid hfast

theorem sr29p108:∀ i ∈ List.range 1,StrictCheckAt 29 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 108) 29 108:=by decide +kernel
  have hfast:StrictAtFast (row 29 108) 29 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 108) 29 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 108) 29 108 hvalid hfast

theorem sr29p109:∀ i ∈ List.range 1,StrictCheckAt 29 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 109) 29 109:=by decide +kernel
  have hfast:StrictAtFast (row 29 109) 29 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 109) 29 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 109) 29 109 hvalid hfast

theorem sr29p110:∀ i ∈ List.range 1,StrictCheckAt 29 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 110) 29 110:=by decide +kernel
  have hfast:StrictAtFast (row 29 110) 29 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 110) 29 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 110) 29 110 hvalid hfast

theorem sr29p111:∀ i ∈ List.range 1,StrictCheckAt 29 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 111) 29 111:=by decide +kernel
  have hfast:StrictAtFast (row 29 111) 29 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 111) 29 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 111) 29 111 hvalid hfast

theorem sr29p112:∀ i ∈ List.range 1,StrictCheckAt 29 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 112) 29 112:=by decide +kernel
  have hfast:StrictAtFast (row 29 112) 29 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 112) 29 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 112) 29 112 hvalid hfast

theorem sr29p113:∀ i ∈ List.range 1,StrictCheckAt 29 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 29 113) 29 113:=by decide +kernel
  have hfast:StrictAtFast (row 29 113) 29 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 29 113) 29 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 29 113) 29 113 hvalid hfast

theorem br29p0:∀ i ∈ List.range 4,BaseCheckAt 29 (0+i):=by decide +kernel

theorem br29p1:∀ i ∈ List.range 4,BaseCheckAt 29 (4+i):=by decide +kernel

theorem br29p2:∀ i ∈ List.range 4,BaseCheckAt 29 (8+i):=by decide +kernel

theorem br29p3:∀ i ∈ List.range 4,BaseCheckAt 29 (12+i):=by decide +kernel

theorem br29p4:∀ i ∈ List.range 4,BaseCheckAt 29 (16+i):=by decide +kernel

theorem br29p5:∀ i ∈ List.range 4,BaseCheckAt 29 (20+i):=by decide +kernel

theorem br29p6:∀ i ∈ List.range 4,BaseCheckAt 29 (24+i):=by decide +kernel

theorem br29p7:∀ i ∈ List.range 4,BaseCheckAt 29 (28+i):=by decide +kernel

theorem br29p8:∀ i ∈ List.range 4,BaseCheckAt 29 (32+i):=by decide +kernel

theorem br29p9:∀ i ∈ List.range 4,BaseCheckAt 29 (36+i):=by decide +kernel

theorem br29p10:∀ i ∈ List.range 4,BaseCheckAt 29 (40+i):=by decide +kernel

theorem br29p11:∀ i ∈ List.range 4,BaseCheckAt 29 (44+i):=by decide +kernel

theorem br29p12:∀ i ∈ List.range 4,BaseCheckAt 29 (48+i):=by decide +kernel

theorem br29p13:∀ i ∈ List.range 4,BaseCheckAt 29 (52+i):=by decide +kernel

theorem br29p14:∀ i ∈ List.range 4,BaseCheckAt 29 (56+i):=by decide +kernel

theorem br29p15:∀ i ∈ List.range 4,BaseCheckAt 29 (60+i):=by decide +kernel



theorem br29p16:∀ i ∈ List.range 4,BaseCheckAt 29 (64+i):=by decide +kernel

theorem br29p17:∀ i ∈ List.range 4,BaseCheckAt 29 (68+i):=by decide +kernel

theorem br29p18:∀ i ∈ List.range 4,BaseCheckAt 29 (72+i):=by decide +kernel

theorem br29p19:∀ i ∈ List.range 4,BaseCheckAt 29 (76+i):=by decide +kernel

theorem br29p20:∀ i ∈ List.range 4,BaseCheckAt 29 (80+i):=by decide +kernel

theorem br29p21:∀ i ∈ List.range 4,BaseCheckAt 29 (84+i):=by decide +kernel

theorem br29p22:∀ i ∈ List.range 4,BaseCheckAt 29 (88+i):=by decide +kernel

theorem br29p23:∀ i ∈ List.range 4,BaseCheckAt 29 (92+i):=by decide +kernel

theorem br29p24:∀ i ∈ List.range 4,BaseCheckAt 29 (96+i):=by decide +kernel

theorem br29p25:∀ i ∈ List.range 4,BaseCheckAt 29 (100+i):=by decide +kernel

theorem br29p26:∀ i ∈ List.range 4,BaseCheckAt 29 (104+i):=by decide +kernel

theorem br29p27:∀ i ∈ List.range 4,BaseCheckAt 29 (108+i):=by decide +kernel

theorem br29p28:∀ i ∈ List.range 2,BaseCheckAt 29 (112+i):=by decide +kernel



theorem cr29:∀ V ∈ List.range 114,CorrectAt 29 V:=by
  intro V hV
  have hv:V < 114:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr29p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr29p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr29p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr29p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr29p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr29p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr29p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr29p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr29p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr29p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr29p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr29p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr29p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr29p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr29p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr29:∀ V ∈ List.range 114,ZeroCheckAt 29 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 29 V (by omega) (by omega) (by omega)
theorem sr29:∀ V ∈ List.range 114,StrictCheckAt 29 V:=by
  intro V hV
  have hv:V < 114:=List.mem_range.mp hV
  by_cases h0_114:V < 57
  · by_cases h0_57:V < 28
    · by_cases h0_28:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr29p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr29p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr29p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr29p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr29p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr29p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr29p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr29p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr29p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr29p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr29p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr29p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr29p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr29p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_28:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr29p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr29p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr29p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr29p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr29p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr29p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr29p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_28:V < 24
          · by_cases h21_24:V < 22
            · have h:=sr29p21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr29p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr29p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr29p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr29p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr29p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr29p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
    · by_cases h28_57:V < 42
      · by_cases h28_42:V < 35
        · by_cases h28_35:V < 31
          · by_cases h28_31:V < 29
            · have h:=sr29p28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr29p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr29p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have h:=sr29p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr29p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
            · by_cases h33_35:V < 34
              · have h:=sr29p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr29p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
        · by_cases h35_42:V < 38
          · by_cases h35_38:V < 36
            · have h:=sr29p35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
            · by_cases h36_38:V < 37
              · have h:=sr29p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr29p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have h:=sr29p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr29p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
            · by_cases h40_42:V < 41
              · have h:=sr29p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr29p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
      · by_cases h42_57:V < 49
        · by_cases h42_49:V < 45
          · by_cases h42_45:V < 43
            · have h:=sr29p42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr29p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr29p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr29p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr29p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr29p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr29p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h49_57:V < 53
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have h:=sr29p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr29p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
            · by_cases h51_53:V < 52
              · have h:=sr29p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr29p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have h:=sr29p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr29p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
            · by_cases h55_57:V < 56
              · have h:=sr29p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr29p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h57_114:V < 85
    · by_cases h57_85:V < 71
      · by_cases h57_71:V < 64
        · by_cases h57_64:V < 60
          · by_cases h57_60:V < 58
            · have h:=sr29p57 (V-57) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
            · by_cases h58_60:V < 59
              · have h:=sr29p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
              · have h:=sr29p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
          · by_cases h60_64:V < 62
            · by_cases h60_62:V < 61
              · have h:=sr29p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr29p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
            · by_cases h62_64:V < 63
              · have h:=sr29p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr29p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
        · by_cases h64_71:V < 67
          · by_cases h64_67:V < 65
            · have h:=sr29p64 (V-64) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
            · by_cases h65_67:V < 66
              · have h:=sr29p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
              · have h:=sr29p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
          · by_cases h67_71:V < 69
            · by_cases h67_69:V < 68
              · have h:=sr29p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
              · have h:=sr29p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
            · by_cases h69_71:V < 70
              · have h:=sr29p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
              · have h:=sr29p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
      · by_cases h71_85:V < 78
        · by_cases h71_78:V < 74
          · by_cases h71_74:V < 72
            · have h:=sr29p71 (V-71) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
            · by_cases h72_74:V < 73
              · have h:=sr29p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr29p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have h:=sr29p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr29p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
            · by_cases h76_78:V < 77
              · have h:=sr29p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr29p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
        · by_cases h78_85:V < 81
          · by_cases h78_81:V < 79
            · have h:=sr29p78 (V-78) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
            · by_cases h79_81:V < 80
              · have h:=sr29p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr29p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have h:=sr29p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr29p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
            · by_cases h83_85:V < 84
              · have h:=sr29p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr29p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
    · by_cases h85_114:V < 99
      · by_cases h85_99:V < 92
        · by_cases h85_92:V < 88
          · by_cases h85_88:V < 86
            · have h:=sr29p85 (V-85) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
            · by_cases h86_88:V < 87
              · have h:=sr29p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr29p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
          · by_cases h88_92:V < 90
            · by_cases h88_90:V < 89
              · have h:=sr29p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr29p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
            · by_cases h90_92:V < 91
              · have h:=sr29p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr29p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
        · by_cases h92_99:V < 95
          · by_cases h92_95:V < 93
            · have h:=sr29p92 (V-92) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
            · by_cases h93_95:V < 94
              · have h:=sr29p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
              · have h:=sr29p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
          · by_cases h95_99:V < 97
            · by_cases h95_97:V < 96
              · have h:=sr29p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
              · have h:=sr29p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
            · by_cases h97_99:V < 98
              · have h:=sr29p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
              · have h:=sr29p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
      · by_cases h99_114:V < 106
        · by_cases h99_106:V < 102
          · by_cases h99_102:V < 100
            · have h:=sr29p99 (V-99) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
            · by_cases h100_102:V < 101
              · have h:=sr29p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr29p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
          · by_cases h102_106:V < 104
            · by_cases h102_104:V < 103
              · have h:=sr29p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr29p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
            · by_cases h104_106:V < 105
              · have h:=sr29p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
              · have h:=sr29p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
        · by_cases h106_114:V < 110
          · by_cases h106_110:V < 108
            · by_cases h106_108:V < 107
              · have h:=sr29p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
              · have h:=sr29p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
            · by_cases h108_110:V < 109
              · have h:=sr29p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
              · have h:=sr29p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
          · by_cases h110_114:V < 112
            · by_cases h110_112:V < 111
              · have h:=sr29p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
              · have h:=sr29p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
            · by_cases h112_114:V < 113
              · have h:=sr29p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
              · have h:=sr29p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h

theorem br29:∀ V ∈ List.range 114,BaseCheckAt 29 V:=by
  intro V hV
  have hv:V < 114:=List.mem_range.mp hV
  by_cases h0_29:V < 56
  · by_cases h0_14:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br29p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br29p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br29p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br29p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br29p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br29p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br29p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_14:V < 40
      · by_cases h7_10:V < 32
        · have h:=br29p7 (V-28) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
        · by_cases h8_10:V < 36
          · have h:=br29p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br29p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
      · by_cases h10_14:V < 48
        · by_cases h10_12:V < 44
          · have h:=br29p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br29p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
        · by_cases h12_14:V < 52
          · have h:=br29p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br29p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
  · by_cases h14_29:V < 84
    · by_cases h14_21:V < 68
      · by_cases h14_17:V < 60
        · have h:=br29p14 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · by_cases h15_17:V < 64
          · have h:=br29p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br29p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br29p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br29p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br29p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br29p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h21_29:V < 100
      · by_cases h21_25:V < 92
        · by_cases h21_23:V < 88
          · have h:=br29p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br29p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h23_25:V < 96
          · have h:=br29p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br29p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h25_29:V < 108
        · by_cases h25_27:V < 104
          · have h:=br29p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br29p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h27_29:V < 112
          · have h:=br29p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br29p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
