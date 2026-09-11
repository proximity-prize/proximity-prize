import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr30p0:∀ i ∈ List.range 8,CorrectAt 30 (0+i):=by decide +kernel

theorem cr30p1:∀ i ∈ List.range 8,CorrectAt 30 (8+i):=by decide +kernel

theorem cr30p2:∀ i ∈ List.range 8,CorrectAt 30 (16+i):=by decide +kernel

theorem cr30p3:∀ i ∈ List.range 8,CorrectAt 30 (24+i):=by decide +kernel

theorem cr30p4:∀ i ∈ List.range 8,CorrectAt 30 (32+i):=by decide +kernel

theorem cr30p5:∀ i ∈ List.range 8,CorrectAt 30 (40+i):=by decide +kernel

theorem cr30p6:∀ i ∈ List.range 8,CorrectAt 30 (48+i):=by decide +kernel

theorem cr30p7:∀ i ∈ List.range 8,CorrectAt 30 (56+i):=by decide +kernel

theorem cr30p8:∀ i ∈ List.range 8,CorrectAt 30 (64+i):=by decide +kernel

theorem cr30p9:∀ i ∈ List.range 8,CorrectAt 30 (72+i):=by decide +kernel

theorem cr30p10:∀ i ∈ List.range 8,CorrectAt 30 (80+i):=by decide +kernel

theorem cr30p11:∀ i ∈ List.range 8,CorrectAt 30 (88+i):=by decide +kernel

theorem cr30p12:∀ i ∈ List.range 8,CorrectAt 30 (96+i):=by decide +kernel

theorem cr30p13:∀ i ∈ List.range 8,CorrectAt 30 (104+i):=by decide +kernel

theorem cr30p14:∀ i ∈ List.range 1,CorrectAt 30 (112+i):=by decide +kernel

theorem sr30p0:∀ i ∈ List.range 1,StrictCheckAt 30 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 0) 30 0:=by decide +kernel
  have hfast:StrictAtFast (row 30 0) 30 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 0) 30 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 0) 30 0 hvalid hfast

theorem sr30p1:∀ i ∈ List.range 1,StrictCheckAt 30 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 1) 30 1:=by decide +kernel
  have hfast:StrictAtFast (row 30 1) 30 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 1) 30 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 1) 30 1 hvalid hfast

theorem sr30p2:∀ i ∈ List.range 1,StrictCheckAt 30 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 2) 30 2:=by decide +kernel
  have hfast:StrictAtFast (row 30 2) 30 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 2) 30 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 2) 30 2 hvalid hfast

theorem sr30p3:∀ i ∈ List.range 1,StrictCheckAt 30 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 3) 30 3:=by decide +kernel
  have hfast:StrictAtFast (row 30 3) 30 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 3) 30 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 3) 30 3 hvalid hfast

theorem sr30p4:∀ i ∈ List.range 1,StrictCheckAt 30 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 4) 30 4:=by decide +kernel
  have hfast:StrictAtFast (row 30 4) 30 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 4) 30 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 4) 30 4 hvalid hfast

theorem sr30p5:∀ i ∈ List.range 1,StrictCheckAt 30 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 5) 30 5:=by decide +kernel
  have hfast:StrictAtFast (row 30 5) 30 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 5) 30 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 5) 30 5 hvalid hfast

theorem sr30p6:∀ i ∈ List.range 1,StrictCheckAt 30 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 6) 30 6:=by decide +kernel
  have hfast:StrictAtFast (row 30 6) 30 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 6) 30 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 6) 30 6 hvalid hfast

theorem sr30p7:∀ i ∈ List.range 1,StrictCheckAt 30 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 7) 30 7:=by decide +kernel
  have hfast:StrictAtFast (row 30 7) 30 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 7) 30 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 7) 30 7 hvalid hfast

theorem sr30p8:∀ i ∈ List.range 1,StrictCheckAt 30 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 8) 30 8:=by decide +kernel
  have hfast:StrictAtFast (row 30 8) 30 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 8) 30 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 8) 30 8 hvalid hfast

theorem sr30p9:∀ i ∈ List.range 1,StrictCheckAt 30 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 9) 30 9:=by decide +kernel
  have hfast:StrictAtFast (row 30 9) 30 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 9) 30 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 9) 30 9 hvalid hfast

theorem sr30p10:∀ i ∈ List.range 1,StrictCheckAt 30 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 10) 30 10:=by decide +kernel
  have hfast:StrictAtFast (row 30 10) 30 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 10) 30 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 10) 30 10 hvalid hfast

theorem sr30p11:∀ i ∈ List.range 1,StrictCheckAt 30 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 11) 30 11:=by decide +kernel
  have hfast:StrictAtFast (row 30 11) 30 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 11) 30 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 11) 30 11 hvalid hfast

theorem sr30p12:∀ i ∈ List.range 1,StrictCheckAt 30 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 12) 30 12:=by decide +kernel
  have hfast:StrictAtFast (row 30 12) 30 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 12) 30 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 12) 30 12 hvalid hfast

theorem sr30p13:∀ i ∈ List.range 1,StrictCheckAt 30 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 13) 30 13:=by decide +kernel
  have hfast:StrictAtFast (row 30 13) 30 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 13) 30 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 13) 30 13 hvalid hfast

theorem sr30p14:∀ i ∈ List.range 1,StrictCheckAt 30 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 14) 30 14:=by decide +kernel
  have hfast:StrictAtFast (row 30 14) 30 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 14) 30 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 14) 30 14 hvalid hfast

theorem sr30p15:∀ i ∈ List.range 1,StrictCheckAt 30 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 15) 30 15:=by decide +kernel
  have hfast:StrictAtFast (row 30 15) 30 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 15) 30 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 15) 30 15 hvalid hfast

theorem sr30p16:∀ i ∈ List.range 1,StrictCheckAt 30 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 16) 30 16:=by decide +kernel
  have hfast:StrictAtFast (row 30 16) 30 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 16) 30 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 16) 30 16 hvalid hfast

theorem sr30p17:∀ i ∈ List.range 1,StrictCheckAt 30 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 17) 30 17:=by decide +kernel
  have hfast:StrictAtFast (row 30 17) 30 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 17) 30 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 17) 30 17 hvalid hfast

theorem sr30p18:∀ i ∈ List.range 1,StrictCheckAt 30 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 18) 30 18:=by decide +kernel
  have hfast:StrictAtFast (row 30 18) 30 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 18) 30 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 18) 30 18 hvalid hfast

theorem sr30p19:∀ i ∈ List.range 1,StrictCheckAt 30 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 19) 30 19:=by decide +kernel
  have hfast:StrictAtFast (row 30 19) 30 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 19) 30 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 19) 30 19 hvalid hfast

theorem sr30p20:∀ i ∈ List.range 1,StrictCheckAt 30 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 20) 30 20:=by decide +kernel
  have hfast:StrictAtFast (row 30 20) 30 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 20) 30 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 20) 30 20 hvalid hfast

theorem sr30p21:∀ i ∈ List.range 1,StrictCheckAt 30 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 21) 30 21:=by decide +kernel
  have hfast:StrictAtFast (row 30 21) 30 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 21) 30 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 21) 30 21 hvalid hfast

theorem sr30p22:∀ i ∈ List.range 1,StrictCheckAt 30 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 22) 30 22:=by decide +kernel
  have hfast:StrictAtFast (row 30 22) 30 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 22) 30 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 22) 30 22 hvalid hfast

theorem sr30p23:∀ i ∈ List.range 1,StrictCheckAt 30 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 23) 30 23:=by decide +kernel
  have hfast:StrictAtFast (row 30 23) 30 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 23) 30 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 23) 30 23 hvalid hfast

theorem sr30p24:∀ i ∈ List.range 1,StrictCheckAt 30 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 24) 30 24:=by decide +kernel
  have hfast:StrictAtFast (row 30 24) 30 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 24) 30 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 24) 30 24 hvalid hfast

theorem sr30p25:∀ i ∈ List.range 1,StrictCheckAt 30 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 25) 30 25:=by decide +kernel
  have hfast:StrictAtFast (row 30 25) 30 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 25) 30 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 25) 30 25 hvalid hfast

theorem sr30p26:∀ i ∈ List.range 1,StrictCheckAt 30 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 26) 30 26:=by decide +kernel
  have hfast:StrictAtFast (row 30 26) 30 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 26) 30 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 26) 30 26 hvalid hfast

theorem sr30p27:∀ i ∈ List.range 1,StrictCheckAt 30 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 27) 30 27:=by decide +kernel
  have hfast:StrictAtFast (row 30 27) 30 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 27) 30 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 27) 30 27 hvalid hfast

theorem sr30p28:∀ i ∈ List.range 1,StrictCheckAt 30 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 28) 30 28:=by decide +kernel
  have hfast:StrictAtFast (row 30 28) 30 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 28) 30 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 28) 30 28 hvalid hfast

theorem sr30p29:∀ i ∈ List.range 1,StrictCheckAt 30 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 29) 30 29:=by decide +kernel
  have hfast:StrictAtFast (row 30 29) 30 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 29) 30 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 29) 30 29 hvalid hfast

theorem sr30p30:∀ i ∈ List.range 1,StrictCheckAt 30 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 30) 30 30:=by decide +kernel
  have hfast:StrictAtFast (row 30 30) 30 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 30) 30 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 30) 30 30 hvalid hfast

theorem sr30p31:∀ i ∈ List.range 1,StrictCheckAt 30 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 31) 30 31:=by decide +kernel
  have hfast:StrictAtFast (row 30 31) 30 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 31) 30 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 31) 30 31 hvalid hfast

theorem sr30p32:∀ i ∈ List.range 1,StrictCheckAt 30 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 32) 30 32:=by decide +kernel
  have hfast:StrictAtFast (row 30 32) 30 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 32) 30 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 32) 30 32 hvalid hfast

theorem sr30p33:∀ i ∈ List.range 1,StrictCheckAt 30 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 33) 30 33:=by decide +kernel
  have hfast:StrictAtFast (row 30 33) 30 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 33) 30 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 33) 30 33 hvalid hfast

theorem sr30p34:∀ i ∈ List.range 1,StrictCheckAt 30 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 34) 30 34:=by decide +kernel
  have hfast:StrictAtFast (row 30 34) 30 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 34) 30 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 34) 30 34 hvalid hfast

theorem sr30p35:∀ i ∈ List.range 1,StrictCheckAt 30 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 35) 30 35:=by decide +kernel
  have hfast:StrictAtFast (row 30 35) 30 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 35) 30 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 35) 30 35 hvalid hfast

theorem sr30p36:∀ i ∈ List.range 1,StrictCheckAt 30 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 36) 30 36:=by decide +kernel
  have hfast:StrictAtFast (row 30 36) 30 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 36) 30 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 36) 30 36 hvalid hfast

theorem sr30p37:∀ i ∈ List.range 1,StrictCheckAt 30 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 37) 30 37:=by decide +kernel
  have hfast:StrictAtFast (row 30 37) 30 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 37) 30 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 37) 30 37 hvalid hfast

theorem sr30p38:∀ i ∈ List.range 1,StrictCheckAt 30 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 38) 30 38:=by decide +kernel
  have hfast:StrictAtFast (row 30 38) 30 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 38) 30 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 38) 30 38 hvalid hfast

theorem sr30p39:∀ i ∈ List.range 1,StrictCheckAt 30 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 39) 30 39:=by decide +kernel
  have hfast:StrictAtFast (row 30 39) 30 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 39) 30 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 39) 30 39 hvalid hfast

theorem sr30p40:∀ i ∈ List.range 1,StrictCheckAt 30 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 40) 30 40:=by decide +kernel
  have hfast:StrictAtFast (row 30 40) 30 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 40) 30 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 40) 30 40 hvalid hfast

theorem sr30p41:∀ i ∈ List.range 1,StrictCheckAt 30 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 41) 30 41:=by decide +kernel
  have hfast:StrictAtFast (row 30 41) 30 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 41) 30 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 41) 30 41 hvalid hfast

theorem sr30p42:∀ i ∈ List.range 1,StrictCheckAt 30 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 42) 30 42:=by decide +kernel
  have hfast:StrictAtFast (row 30 42) 30 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 42) 30 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 42) 30 42 hvalid hfast

theorem sr30p43:∀ i ∈ List.range 1,StrictCheckAt 30 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 43) 30 43:=by decide +kernel
  have hfast:StrictAtFast (row 30 43) 30 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 43) 30 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 43) 30 43 hvalid hfast

theorem sr30p44:∀ i ∈ List.range 1,StrictCheckAt 30 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 44) 30 44:=by decide +kernel
  have hfast:StrictAtFast (row 30 44) 30 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 44) 30 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 44) 30 44 hvalid hfast

theorem sr30p45:∀ i ∈ List.range 1,StrictCheckAt 30 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 45) 30 45:=by decide +kernel
  have hfast:StrictAtFast (row 30 45) 30 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 45) 30 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 45) 30 45 hvalid hfast

theorem sr30p46:∀ i ∈ List.range 1,StrictCheckAt 30 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 46) 30 46:=by decide +kernel
  have hfast:StrictAtFast (row 30 46) 30 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 46) 30 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 46) 30 46 hvalid hfast

theorem sr30p47:∀ i ∈ List.range 1,StrictCheckAt 30 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 47) 30 47:=by decide +kernel
  have hfast:StrictAtFast (row 30 47) 30 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 47) 30 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 47) 30 47 hvalid hfast

theorem sr30p48:∀ i ∈ List.range 1,StrictCheckAt 30 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 48) 30 48:=by decide +kernel
  have hfast:StrictAtFast (row 30 48) 30 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 48) 30 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 48) 30 48 hvalid hfast

theorem sr30p49:∀ i ∈ List.range 1,StrictCheckAt 30 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 49) 30 49:=by decide +kernel
  have hfast:StrictAtFast (row 30 49) 30 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 49) 30 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 49) 30 49 hvalid hfast

theorem sr30p50:∀ i ∈ List.range 1,StrictCheckAt 30 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 50) 30 50:=by decide +kernel
  have hfast:StrictAtFast (row 30 50) 30 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 50) 30 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 50) 30 50 hvalid hfast

theorem sr30p51:∀ i ∈ List.range 1,StrictCheckAt 30 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 51) 30 51:=by decide +kernel
  have hfast:StrictAtFast (row 30 51) 30 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 51) 30 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 51) 30 51 hvalid hfast

theorem sr30p52:∀ i ∈ List.range 1,StrictCheckAt 30 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 52) 30 52:=by decide +kernel
  have hfast:StrictAtFast (row 30 52) 30 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 52) 30 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 52) 30 52 hvalid hfast

theorem sr30p53:∀ i ∈ List.range 1,StrictCheckAt 30 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 53) 30 53:=by decide +kernel
  have hfast:StrictAtFast (row 30 53) 30 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 53) 30 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 53) 30 53 hvalid hfast

theorem sr30p54:∀ i ∈ List.range 1,StrictCheckAt 30 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 54) 30 54:=by decide +kernel
  have hfast:StrictAtFast (row 30 54) 30 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 54) 30 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 54) 30 54 hvalid hfast

theorem sr30p55:∀ i ∈ List.range 1,StrictCheckAt 30 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 55) 30 55:=by decide +kernel
  have hfast:StrictAtFast (row 30 55) 30 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 55) 30 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 55) 30 55 hvalid hfast

theorem sr30p56:∀ i ∈ List.range 1,StrictCheckAt 30 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 56) 30 56:=by decide +kernel
  have hfast:StrictAtFast (row 30 56) 30 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 56) 30 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 56) 30 56 hvalid hfast

theorem sr30p57:∀ i ∈ List.range 1,StrictCheckAt 30 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 57) 30 57:=by decide +kernel
  have hfast:StrictAtFast (row 30 57) 30 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 57) 30 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 57) 30 57 hvalid hfast

theorem sr30p58:∀ i ∈ List.range 1,StrictCheckAt 30 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 58) 30 58:=by decide +kernel
  have hfast:StrictAtFast (row 30 58) 30 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 58) 30 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 58) 30 58 hvalid hfast

theorem sr30p59:∀ i ∈ List.range 1,StrictCheckAt 30 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 59) 30 59:=by decide +kernel
  have hfast:StrictAtFast (row 30 59) 30 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 59) 30 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 59) 30 59 hvalid hfast

theorem sr30p60:∀ i ∈ List.range 1,StrictCheckAt 30 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 60) 30 60:=by decide +kernel
  have hfast:StrictAtFast (row 30 60) 30 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 60) 30 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 60) 30 60 hvalid hfast

theorem sr30p61:∀ i ∈ List.range 1,StrictCheckAt 30 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 61) 30 61:=by decide +kernel
  have hfast:StrictAtFast (row 30 61) 30 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 61) 30 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 61) 30 61 hvalid hfast

theorem sr30p62:∀ i ∈ List.range 1,StrictCheckAt 30 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 62) 30 62:=by decide +kernel
  have hfast:StrictAtFast (row 30 62) 30 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 62) 30 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 62) 30 62 hvalid hfast

theorem sr30p63:∀ i ∈ List.range 1,StrictCheckAt 30 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 63) 30 63:=by decide +kernel
  have hfast:StrictAtFast (row 30 63) 30 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 63) 30 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 63) 30 63 hvalid hfast

theorem sr30p64:∀ i ∈ List.range 1,StrictCheckAt 30 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 64) 30 64:=by decide +kernel
  have hfast:StrictAtFast (row 30 64) 30 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 64) 30 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 64) 30 64 hvalid hfast

theorem sr30p65:∀ i ∈ List.range 1,StrictCheckAt 30 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 65) 30 65:=by decide +kernel
  have hfast:StrictAtFast (row 30 65) 30 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 65) 30 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 65) 30 65 hvalid hfast

theorem sr30p66:∀ i ∈ List.range 1,StrictCheckAt 30 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 66) 30 66:=by decide +kernel
  have hfast:StrictAtFast (row 30 66) 30 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 66) 30 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 66) 30 66 hvalid hfast

theorem sr30p67:∀ i ∈ List.range 1,StrictCheckAt 30 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 67) 30 67:=by decide +kernel
  have hfast:StrictAtFast (row 30 67) 30 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 67) 30 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 67) 30 67 hvalid hfast

theorem sr30p68:∀ i ∈ List.range 1,StrictCheckAt 30 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 68) 30 68:=by decide +kernel
  have hfast:StrictAtFast (row 30 68) 30 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 68) 30 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 68) 30 68 hvalid hfast

theorem sr30p69:∀ i ∈ List.range 1,StrictCheckAt 30 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 69) 30 69:=by decide +kernel
  have hfast:StrictAtFast (row 30 69) 30 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 69) 30 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 69) 30 69 hvalid hfast

theorem sr30p70:∀ i ∈ List.range 1,StrictCheckAt 30 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 70) 30 70:=by decide +kernel
  have hfast:StrictAtFast (row 30 70) 30 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 70) 30 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 70) 30 70 hvalid hfast

theorem sr30p71:∀ i ∈ List.range 1,StrictCheckAt 30 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 71) 30 71:=by decide +kernel
  have hfast:StrictAtFast (row 30 71) 30 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 71) 30 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 71) 30 71 hvalid hfast

theorem sr30p72:∀ i ∈ List.range 1,StrictCheckAt 30 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 72) 30 72:=by decide +kernel
  have hfast:StrictAtFast (row 30 72) 30 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 72) 30 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 72) 30 72 hvalid hfast

theorem sr30p73:∀ i ∈ List.range 1,StrictCheckAt 30 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 73) 30 73:=by decide +kernel
  have hfast:StrictAtFast (row 30 73) 30 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 73) 30 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 73) 30 73 hvalid hfast

theorem sr30p74:∀ i ∈ List.range 1,StrictCheckAt 30 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 74) 30 74:=by decide +kernel
  have hfast:StrictAtFast (row 30 74) 30 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 74) 30 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 74) 30 74 hvalid hfast

theorem sr30p75:∀ i ∈ List.range 1,StrictCheckAt 30 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 75) 30 75:=by decide +kernel
  have hfast:StrictAtFast (row 30 75) 30 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 75) 30 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 75) 30 75 hvalid hfast

theorem sr30p76:∀ i ∈ List.range 1,StrictCheckAt 30 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 76) 30 76:=by decide +kernel
  have hfast:StrictAtFast (row 30 76) 30 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 76) 30 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 76) 30 76 hvalid hfast

theorem sr30p77:∀ i ∈ List.range 1,StrictCheckAt 30 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 77) 30 77:=by decide +kernel
  have hfast:StrictAtFast (row 30 77) 30 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 77) 30 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 77) 30 77 hvalid hfast

theorem sr30p78:∀ i ∈ List.range 1,StrictCheckAt 30 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 78) 30 78:=by decide +kernel
  have hfast:StrictAtFast (row 30 78) 30 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 78) 30 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 78) 30 78 hvalid hfast

theorem sr30p79:∀ i ∈ List.range 1,StrictCheckAt 30 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 79) 30 79:=by decide +kernel
  have hfast:StrictAtFast (row 30 79) 30 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 79) 30 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 79) 30 79 hvalid hfast

theorem sr30p80:∀ i ∈ List.range 1,StrictCheckAt 30 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 80) 30 80:=by decide +kernel
  have hfast:StrictAtFast (row 30 80) 30 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 80) 30 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 80) 30 80 hvalid hfast

theorem sr30p81:∀ i ∈ List.range 1,StrictCheckAt 30 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 81) 30 81:=by decide +kernel
  have hfast:StrictAtFast (row 30 81) 30 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 81) 30 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 81) 30 81 hvalid hfast

theorem sr30p82:∀ i ∈ List.range 1,StrictCheckAt 30 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 82) 30 82:=by decide +kernel
  have hfast:StrictAtFast (row 30 82) 30 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 82) 30 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 82) 30 82 hvalid hfast

theorem sr30p83:∀ i ∈ List.range 1,StrictCheckAt 30 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 83) 30 83:=by decide +kernel
  have hfast:StrictAtFast (row 30 83) 30 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 83) 30 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 83) 30 83 hvalid hfast

theorem sr30p84:∀ i ∈ List.range 1,StrictCheckAt 30 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 84) 30 84:=by decide +kernel
  have hfast:StrictAtFast (row 30 84) 30 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 84) 30 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 84) 30 84 hvalid hfast

theorem sr30p85:∀ i ∈ List.range 1,StrictCheckAt 30 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 85) 30 85:=by decide +kernel
  have hfast:StrictAtFast (row 30 85) 30 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 85) 30 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 85) 30 85 hvalid hfast

theorem sr30p86:∀ i ∈ List.range 1,StrictCheckAt 30 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 86) 30 86:=by decide +kernel
  have hfast:StrictAtFast (row 30 86) 30 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 86) 30 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 86) 30 86 hvalid hfast

theorem sr30p87:∀ i ∈ List.range 1,StrictCheckAt 30 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 87) 30 87:=by decide +kernel
  have hfast:StrictAtFast (row 30 87) 30 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 87) 30 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 87) 30 87 hvalid hfast

theorem sr30p88:∀ i ∈ List.range 1,StrictCheckAt 30 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 88) 30 88:=by decide +kernel
  have hfast:StrictAtFast (row 30 88) 30 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 88) 30 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 88) 30 88 hvalid hfast

theorem sr30p89:∀ i ∈ List.range 1,StrictCheckAt 30 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 89) 30 89:=by decide +kernel
  have hfast:StrictAtFast (row 30 89) 30 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 89) 30 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 89) 30 89 hvalid hfast

theorem sr30p90:∀ i ∈ List.range 1,StrictCheckAt 30 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 90) 30 90:=by decide +kernel
  have hfast:StrictAtFast (row 30 90) 30 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 90) 30 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 90) 30 90 hvalid hfast

theorem sr30p91:∀ i ∈ List.range 1,StrictCheckAt 30 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 91) 30 91:=by decide +kernel
  have hfast:StrictAtFast (row 30 91) 30 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 91) 30 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 91) 30 91 hvalid hfast

theorem sr30p92:∀ i ∈ List.range 1,StrictCheckAt 30 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 92) 30 92:=by decide +kernel
  have hfast:StrictAtFast (row 30 92) 30 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 92) 30 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 92) 30 92 hvalid hfast

theorem sr30p93:∀ i ∈ List.range 1,StrictCheckAt 30 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 93) 30 93:=by decide +kernel
  have hfast:StrictAtFast (row 30 93) 30 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 93) 30 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 93) 30 93 hvalid hfast

theorem sr30p94:∀ i ∈ List.range 1,StrictCheckAt 30 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 94) 30 94:=by decide +kernel
  have hfast:StrictAtFast (row 30 94) 30 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 94) 30 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 94) 30 94 hvalid hfast

theorem sr30p95:∀ i ∈ List.range 1,StrictCheckAt 30 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 95) 30 95:=by decide +kernel
  have hfast:StrictAtFast (row 30 95) 30 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 95) 30 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 95) 30 95 hvalid hfast

theorem sr30p96:∀ i ∈ List.range 1,StrictCheckAt 30 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 96) 30 96:=by decide +kernel
  have hfast:StrictAtFast (row 30 96) 30 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 96) 30 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 96) 30 96 hvalid hfast

theorem sr30p97:∀ i ∈ List.range 1,StrictCheckAt 30 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 97) 30 97:=by decide +kernel
  have hfast:StrictAtFast (row 30 97) 30 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 97) 30 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 97) 30 97 hvalid hfast

theorem sr30p98:∀ i ∈ List.range 1,StrictCheckAt 30 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 98) 30 98:=by decide +kernel
  have hfast:StrictAtFast (row 30 98) 30 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 98) 30 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 98) 30 98 hvalid hfast

theorem sr30p99:∀ i ∈ List.range 1,StrictCheckAt 30 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 99) 30 99:=by decide +kernel
  have hfast:StrictAtFast (row 30 99) 30 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 99) 30 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 99) 30 99 hvalid hfast

theorem sr30p100:∀ i ∈ List.range 1,StrictCheckAt 30 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 100) 30 100:=by decide +kernel
  have hfast:StrictAtFast (row 30 100) 30 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 100) 30 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 100) 30 100 hvalid hfast

theorem sr30p101:∀ i ∈ List.range 1,StrictCheckAt 30 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 101) 30 101:=by decide +kernel
  have hfast:StrictAtFast (row 30 101) 30 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 101) 30 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 101) 30 101 hvalid hfast

theorem sr30p102:∀ i ∈ List.range 1,StrictCheckAt 30 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 102) 30 102:=by decide +kernel
  have hfast:StrictAtFast (row 30 102) 30 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 102) 30 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 102) 30 102 hvalid hfast

theorem sr30p103:∀ i ∈ List.range 1,StrictCheckAt 30 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 103) 30 103:=by decide +kernel
  have hfast:StrictAtFast (row 30 103) 30 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 103) 30 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 103) 30 103 hvalid hfast

theorem sr30p104:∀ i ∈ List.range 1,StrictCheckAt 30 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 104) 30 104:=by decide +kernel
  have hfast:StrictAtFast (row 30 104) 30 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 104) 30 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 104) 30 104 hvalid hfast

theorem sr30p105:∀ i ∈ List.range 1,StrictCheckAt 30 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 105) 30 105:=by decide +kernel
  have hfast:StrictAtFast (row 30 105) 30 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 105) 30 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 105) 30 105 hvalid hfast

theorem sr30p106:∀ i ∈ List.range 1,StrictCheckAt 30 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 106) 30 106:=by decide +kernel
  have hfast:StrictAtFast (row 30 106) 30 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 106) 30 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 106) 30 106 hvalid hfast

theorem sr30p107:∀ i ∈ List.range 1,StrictCheckAt 30 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 107) 30 107:=by decide +kernel
  have hfast:StrictAtFast (row 30 107) 30 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 107) 30 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 107) 30 107 hvalid hfast

theorem sr30p108:∀ i ∈ List.range 1,StrictCheckAt 30 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 108) 30 108:=by decide +kernel
  have hfast:StrictAtFast (row 30 108) 30 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 108) 30 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 108) 30 108 hvalid hfast

theorem sr30p109:∀ i ∈ List.range 1,StrictCheckAt 30 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 109) 30 109:=by decide +kernel
  have hfast:StrictAtFast (row 30 109) 30 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 109) 30 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 109) 30 109 hvalid hfast

theorem sr30p110:∀ i ∈ List.range 1,StrictCheckAt 30 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 110) 30 110:=by decide +kernel
  have hfast:StrictAtFast (row 30 110) 30 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 110) 30 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 110) 30 110 hvalid hfast

theorem sr30p111:∀ i ∈ List.range 1,StrictCheckAt 30 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 111) 30 111:=by decide +kernel
  have hfast:StrictAtFast (row 30 111) 30 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 111) 30 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 111) 30 111 hvalid hfast

theorem sr30p112:∀ i ∈ List.range 1,StrictCheckAt 30 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 30 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 30 112) 30 112:=by decide +kernel
  have hfast:StrictAtFast (row 30 112) 30 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 30 112) 30 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 30 112) 30 112 hvalid hfast

theorem br30p0:∀ i ∈ List.range 4,BaseCheckAt 30 (0+i):=by decide +kernel

theorem br30p1:∀ i ∈ List.range 4,BaseCheckAt 30 (4+i):=by decide +kernel

theorem br30p2:∀ i ∈ List.range 4,BaseCheckAt 30 (8+i):=by decide +kernel

theorem br30p3:∀ i ∈ List.range 4,BaseCheckAt 30 (12+i):=by decide +kernel

theorem br30p4:∀ i ∈ List.range 4,BaseCheckAt 30 (16+i):=by decide +kernel

theorem br30p5:∀ i ∈ List.range 4,BaseCheckAt 30 (20+i):=by decide +kernel

theorem br30p6:∀ i ∈ List.range 4,BaseCheckAt 30 (24+i):=by decide +kernel

theorem br30p7:∀ i ∈ List.range 4,BaseCheckAt 30 (28+i):=by decide +kernel

theorem br30p8:∀ i ∈ List.range 4,BaseCheckAt 30 (32+i):=by decide +kernel

theorem br30p9:∀ i ∈ List.range 4,BaseCheckAt 30 (36+i):=by decide +kernel

theorem br30p10:∀ i ∈ List.range 4,BaseCheckAt 30 (40+i):=by decide +kernel

theorem br30p11:∀ i ∈ List.range 4,BaseCheckAt 30 (44+i):=by decide +kernel

theorem br30p12:∀ i ∈ List.range 4,BaseCheckAt 30 (48+i):=by decide +kernel

theorem br30p13:∀ i ∈ List.range 4,BaseCheckAt 30 (52+i):=by decide +kernel

theorem br30p14:∀ i ∈ List.range 4,BaseCheckAt 30 (56+i):=by decide +kernel

theorem br30p15:∀ i ∈ List.range 4,BaseCheckAt 30 (60+i):=by decide +kernel



theorem br30p16:∀ i ∈ List.range 4,BaseCheckAt 30 (64+i):=by decide +kernel

theorem br30p17:∀ i ∈ List.range 4,BaseCheckAt 30 (68+i):=by decide +kernel

theorem br30p18:∀ i ∈ List.range 4,BaseCheckAt 30 (72+i):=by decide +kernel

theorem br30p19:∀ i ∈ List.range 4,BaseCheckAt 30 (76+i):=by decide +kernel

theorem br30p20:∀ i ∈ List.range 4,BaseCheckAt 30 (80+i):=by decide +kernel

theorem br30p21:∀ i ∈ List.range 4,BaseCheckAt 30 (84+i):=by decide +kernel

theorem br30p22:∀ i ∈ List.range 4,BaseCheckAt 30 (88+i):=by decide +kernel

theorem br30p23:∀ i ∈ List.range 4,BaseCheckAt 30 (92+i):=by decide +kernel

theorem br30p24:∀ i ∈ List.range 4,BaseCheckAt 30 (96+i):=by decide +kernel

theorem br30p25:∀ i ∈ List.range 4,BaseCheckAt 30 (100+i):=by decide +kernel

theorem br30p26:∀ i ∈ List.range 4,BaseCheckAt 30 (104+i):=by decide +kernel

theorem br30p27:∀ i ∈ List.range 4,BaseCheckAt 30 (108+i):=by decide +kernel

theorem br30p28:∀ i ∈ List.range 1,BaseCheckAt 30 (112+i):=by decide +kernel



theorem cr30:∀ V ∈ List.range 113,CorrectAt 30 V:=by
  intro V hV
  have hv:V < 113:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr30p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr30p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr30p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr30p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr30p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr30p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr30p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr30p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr30p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr30p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr30p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr30p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr30p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr30p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr30p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr30:∀ V ∈ List.range 113,ZeroCheckAt 30 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 30 V (by omega) (by omega) (by omega)
theorem sr30:∀ V ∈ List.range 113,StrictCheckAt 30 V:=by
  intro V hV
  have hv:V < 113:=List.mem_range.mp hV
  by_cases h0_113:V < 56
  · by_cases h0_56:V < 28
    · by_cases h0_28:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr30p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr30p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr30p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr30p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr30p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr30p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr30p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr30p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr30p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr30p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr30p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr30p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr30p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr30p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_28:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr30p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr30p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr30p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr30p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr30p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr30p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr30p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_28:V < 24
          · by_cases h21_24:V < 22
            · have h:=sr30p21 (V-21) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr30p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr30p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr30p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr30p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr30p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr30p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
    · by_cases h28_56:V < 42
      · by_cases h28_42:V < 35
        · by_cases h28_35:V < 31
          · by_cases h28_31:V < 29
            · have h:=sr30p28 (V-28) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
            · by_cases h29_31:V < 30
              · have h:=sr30p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
              · have h:=sr30p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
          · by_cases h31_35:V < 33
            · by_cases h31_33:V < 32
              · have h:=sr30p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
              · have h:=sr30p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
            · by_cases h33_35:V < 34
              · have h:=sr30p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr30p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
        · by_cases h35_42:V < 38
          · by_cases h35_38:V < 36
            · have h:=sr30p35 (V-35) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
            · by_cases h36_38:V < 37
              · have h:=sr30p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr30p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
          · by_cases h38_42:V < 40
            · by_cases h38_40:V < 39
              · have h:=sr30p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr30p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
            · by_cases h40_42:V < 41
              · have h:=sr30p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr30p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
      · by_cases h42_56:V < 49
        · by_cases h42_49:V < 45
          · by_cases h42_45:V < 43
            · have h:=sr30p42 (V-42) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr30p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr30p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr30p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr30p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr30p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr30p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h49_56:V < 52
          · by_cases h49_52:V < 50
            · have h:=sr30p49 (V-49) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
            · by_cases h50_52:V < 51
              · have h:=sr30p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
              · have h:=sr30p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
          · by_cases h52_56:V < 54
            · by_cases h52_54:V < 53
              · have h:=sr30p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
              · have h:=sr30p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
            · by_cases h54_56:V < 55
              · have h:=sr30p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
              · have h:=sr30p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
  · by_cases h56_113:V < 84
    · by_cases h56_84:V < 70
      · by_cases h56_70:V < 63
        · by_cases h56_63:V < 59
          · by_cases h56_59:V < 57
            · have h:=sr30p56 (V-56) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
            · by_cases h57_59:V < 58
              · have h:=sr30p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr30p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
          · by_cases h59_63:V < 61
            · by_cases h59_61:V < 60
              · have h:=sr30p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr30p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
            · by_cases h61_63:V < 62
              · have h:=sr30p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr30p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
        · by_cases h63_70:V < 66
          · by_cases h63_66:V < 64
            · have h:=sr30p63 (V-63) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
            · by_cases h64_66:V < 65
              · have h:=sr30p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr30p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have h:=sr30p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr30p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
            · by_cases h68_70:V < 69
              · have h:=sr30p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr30p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
      · by_cases h70_84:V < 77
        · by_cases h70_77:V < 73
          · by_cases h70_73:V < 71
            · have h:=sr30p70 (V-70) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
            · by_cases h71_73:V < 72
              · have h:=sr30p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
              · have h:=sr30p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · by_cases h73_77:V < 75
            · by_cases h73_75:V < 74
              · have h:=sr30p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
              · have h:=sr30p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
            · by_cases h75_77:V < 76
              · have h:=sr30p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr30p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
        · by_cases h77_84:V < 80
          · by_cases h77_80:V < 78
            · have h:=sr30p77 (V-77) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
            · by_cases h78_80:V < 79
              · have h:=sr30p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr30p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
          · by_cases h80_84:V < 82
            · by_cases h80_82:V < 81
              · have h:=sr30p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr30p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
            · by_cases h82_84:V < 83
              · have h:=sr30p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr30p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
    · by_cases h84_113:V < 98
      · by_cases h84_98:V < 91
        · by_cases h84_91:V < 87
          · by_cases h84_87:V < 85
            · have h:=sr30p84 (V-84) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
            · by_cases h85_87:V < 86
              · have h:=sr30p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr30p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
          · by_cases h87_91:V < 89
            · by_cases h87_89:V < 88
              · have h:=sr30p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr30p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
            · by_cases h89_91:V < 90
              · have h:=sr30p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
              · have h:=sr30p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
        · by_cases h91_98:V < 94
          · by_cases h91_94:V < 92
            · have h:=sr30p91 (V-91) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr30p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr30p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
          · by_cases h94_98:V < 96
            · by_cases h94_96:V < 95
              · have h:=sr30p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr30p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
            · by_cases h96_98:V < 97
              · have h:=sr30p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr30p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
      · by_cases h98_113:V < 105
        · by_cases h98_105:V < 101
          · by_cases h98_101:V < 99
            · have h:=sr30p98 (V-98) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
            · by_cases h99_101:V < 100
              · have h:=sr30p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr30p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · by_cases h101_105:V < 103
            · by_cases h101_103:V < 102
              · have h:=sr30p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr30p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
            · by_cases h103_105:V < 104
              · have h:=sr30p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr30p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h105_113:V < 109
          · by_cases h105_109:V < 107
            · by_cases h105_107:V < 106
              · have h:=sr30p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr30p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
            · by_cases h107_109:V < 108
              · have h:=sr30p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr30p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · by_cases h109_113:V < 111
            · by_cases h109_111:V < 110
              · have h:=sr30p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr30p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
            · by_cases h111_113:V < 112
              · have h:=sr30p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr30p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem br30:∀ V ∈ List.range 113,BaseCheckAt 30 V:=by
  intro V hV
  have hv:V < 113:=List.mem_range.mp hV
  by_cases h0_29:V < 56
  · by_cases h0_14:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br30p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br30p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br30p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br30p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br30p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br30p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br30p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_14:V < 40
      · by_cases h7_10:V < 32
        · have h:=br30p7 (V-28) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
        · by_cases h8_10:V < 36
          · have h:=br30p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br30p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
      · by_cases h10_14:V < 48
        · by_cases h10_12:V < 44
          · have h:=br30p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br30p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
        · by_cases h12_14:V < 52
          · have h:=br30p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br30p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
  · by_cases h14_29:V < 84
    · by_cases h14_21:V < 68
      · by_cases h14_17:V < 60
        · have h:=br30p14 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · by_cases h15_17:V < 64
          · have h:=br30p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · have h:=br30p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h17_21:V < 76
        · by_cases h17_19:V < 72
          · have h:=br30p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
          · have h:=br30p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · by_cases h19_21:V < 80
          · have h:=br30p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · have h:=br30p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h21_29:V < 100
      · by_cases h21_25:V < 92
        · by_cases h21_23:V < 88
          · have h:=br30p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · have h:=br30p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · by_cases h23_25:V < 96
          · have h:=br30p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
          · have h:=br30p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h25_29:V < 108
        · by_cases h25_27:V < 104
          · have h:=br30p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
          · have h:=br30p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · by_cases h27_29:V < 112
          · have h:=br30p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
          · have h:=br30p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
