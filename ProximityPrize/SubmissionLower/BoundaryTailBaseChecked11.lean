import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr11p0:∀ i ∈ List.range 8,CorrectAt 11 (0+i):=by decide +kernel

theorem cr11p1:∀ i ∈ List.range 8,CorrectAt 11 (8+i):=by decide +kernel

theorem cr11p2:∀ i ∈ List.range 8,CorrectAt 11 (16+i):=by decide +kernel

theorem cr11p3:∀ i ∈ List.range 8,CorrectAt 11 (24+i):=by decide +kernel

theorem cr11p4:∀ i ∈ List.range 8,CorrectAt 11 (32+i):=by decide +kernel

theorem cr11p5:∀ i ∈ List.range 8,CorrectAt 11 (40+i):=by decide +kernel

theorem cr11p6:∀ i ∈ List.range 8,CorrectAt 11 (48+i):=by decide +kernel

theorem cr11p7:∀ i ∈ List.range 8,CorrectAt 11 (56+i):=by decide +kernel

theorem cr11p8:∀ i ∈ List.range 8,CorrectAt 11 (64+i):=by decide +kernel

theorem cr11p9:∀ i ∈ List.range 8,CorrectAt 11 (72+i):=by decide +kernel

theorem cr11p10:∀ i ∈ List.range 8,CorrectAt 11 (80+i):=by decide +kernel

theorem cr11p11:∀ i ∈ List.range 8,CorrectAt 11 (88+i):=by decide +kernel

theorem cr11p12:∀ i ∈ List.range 8,CorrectAt 11 (96+i):=by decide +kernel

theorem cr11p13:∀ i ∈ List.range 8,CorrectAt 11 (104+i):=by decide +kernel

theorem cr11p14:∀ i ∈ List.range 8,CorrectAt 11 (112+i):=by decide +kernel

theorem cr11p15:∀ i ∈ List.range 8,CorrectAt 11 (120+i):=by decide +kernel

theorem cr11p16:∀ i ∈ List.range 4,CorrectAt 11 (128+i):=by decide +kernel

theorem sr11p0:∀ i ∈ List.range 1,StrictCheckAt 11 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 0) 11 0:=by decide +kernel
  have hfast:StrictAtFast (row 11 0) 11 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 0) 11 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 0) 11 0 hvalid hfast

theorem sr11p1:∀ i ∈ List.range 1,StrictCheckAt 11 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 1) 11 1:=by decide +kernel
  have hfast:StrictAtFast (row 11 1) 11 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 1) 11 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 1) 11 1 hvalid hfast

theorem sr11p2:∀ i ∈ List.range 1,StrictCheckAt 11 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 2) 11 2:=by decide +kernel
  have hfast:StrictAtFast (row 11 2) 11 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 2) 11 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 2) 11 2 hvalid hfast

theorem sr11p3:∀ i ∈ List.range 1,StrictCheckAt 11 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 3) 11 3:=by decide +kernel
  have hfast:StrictAtFast (row 11 3) 11 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 3) 11 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 3) 11 3 hvalid hfast

theorem sr11p4:∀ i ∈ List.range 1,StrictCheckAt 11 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 4) 11 4:=by decide +kernel
  have hfast:StrictAtFast (row 11 4) 11 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 4) 11 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 4) 11 4 hvalid hfast

theorem sr11p5:∀ i ∈ List.range 1,StrictCheckAt 11 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 5) 11 5:=by decide +kernel
  have hfast:StrictAtFast (row 11 5) 11 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 5) 11 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 5) 11 5 hvalid hfast

theorem sr11p6:∀ i ∈ List.range 1,StrictCheckAt 11 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 6) 11 6:=by decide +kernel
  have hfast:StrictAtFast (row 11 6) 11 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 6) 11 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 6) 11 6 hvalid hfast

theorem sr11p7:∀ i ∈ List.range 1,StrictCheckAt 11 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 7) 11 7:=by decide +kernel
  have hfast:StrictAtFast (row 11 7) 11 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 7) 11 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 7) 11 7 hvalid hfast

theorem sr11p8:∀ i ∈ List.range 1,StrictCheckAt 11 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 8) 11 8:=by decide +kernel
  have hfast:StrictAtFast (row 11 8) 11 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 8) 11 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 8) 11 8 hvalid hfast

theorem sr11p9:∀ i ∈ List.range 1,StrictCheckAt 11 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 9) 11 9:=by decide +kernel
  have hfast:StrictAtFast (row 11 9) 11 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 9) 11 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 9) 11 9 hvalid hfast

theorem sr11p10:∀ i ∈ List.range 1,StrictCheckAt 11 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 10) 11 10:=by decide +kernel
  have hfast:StrictAtFast (row 11 10) 11 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 10) 11 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 10) 11 10 hvalid hfast

theorem sr11p11:∀ i ∈ List.range 1,StrictCheckAt 11 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 11) 11 11:=by decide +kernel
  have hfast:StrictAtFast (row 11 11) 11 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 11) 11 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 11) 11 11 hvalid hfast

theorem sr11p12:∀ i ∈ List.range 1,StrictCheckAt 11 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 12) 11 12:=by decide +kernel
  have hfast:StrictAtFast (row 11 12) 11 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 12) 11 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 12) 11 12 hvalid hfast

theorem sr11p13:∀ i ∈ List.range 1,StrictCheckAt 11 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 13) 11 13:=by decide +kernel
  have hfast:StrictAtFast (row 11 13) 11 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 13) 11 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 13) 11 13 hvalid hfast

theorem sr11p14:∀ i ∈ List.range 1,StrictCheckAt 11 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 14) 11 14:=by decide +kernel
  have hfast:StrictAtFast (row 11 14) 11 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 14) 11 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 14) 11 14 hvalid hfast

theorem sr11p15:∀ i ∈ List.range 1,StrictCheckAt 11 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 15) 11 15:=by decide +kernel
  have hfast:StrictAtFast (row 11 15) 11 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 15) 11 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 15) 11 15 hvalid hfast

theorem sr11p16:∀ i ∈ List.range 1,StrictCheckAt 11 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 16) 11 16:=by decide +kernel
  have hfast:StrictAtFast (row 11 16) 11 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 16) 11 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 16) 11 16 hvalid hfast

theorem sr11p17:∀ i ∈ List.range 1,StrictCheckAt 11 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 17) 11 17:=by decide +kernel
  have hfast:StrictAtFast (row 11 17) 11 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 17) 11 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 17) 11 17 hvalid hfast

theorem sr11p18:∀ i ∈ List.range 1,StrictCheckAt 11 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 18) 11 18:=by decide +kernel
  have hfast:StrictAtFast (row 11 18) 11 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 18) 11 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 18) 11 18 hvalid hfast

theorem sr11p19:∀ i ∈ List.range 1,StrictCheckAt 11 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 19) 11 19:=by decide +kernel
  have hfast:StrictAtFast (row 11 19) 11 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 19) 11 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 19) 11 19 hvalid hfast

theorem sr11p20:∀ i ∈ List.range 1,StrictCheckAt 11 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 20) 11 20:=by decide +kernel
  have hfast:StrictAtFast (row 11 20) 11 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 20) 11 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 20) 11 20 hvalid hfast

theorem sr11p21:∀ i ∈ List.range 1,StrictCheckAt 11 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 21) 11 21:=by decide +kernel
  have hfast:StrictAtFast (row 11 21) 11 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 21) 11 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 21) 11 21 hvalid hfast

theorem sr11p22:∀ i ∈ List.range 1,StrictCheckAt 11 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 22) 11 22:=by decide +kernel
  have hfast:StrictAtFast (row 11 22) 11 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 22) 11 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 22) 11 22 hvalid hfast

theorem sr11p23:∀ i ∈ List.range 1,StrictCheckAt 11 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 23) 11 23:=by decide +kernel
  have hfast:StrictAtFast (row 11 23) 11 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 23) 11 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 23) 11 23 hvalid hfast

theorem sr11p24:∀ i ∈ List.range 1,StrictCheckAt 11 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 24) 11 24:=by decide +kernel
  have hfast:StrictAtFast (row 11 24) 11 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 24) 11 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 24) 11 24 hvalid hfast

theorem sr11p25:∀ i ∈ List.range 1,StrictCheckAt 11 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 25) 11 25:=by decide +kernel
  have hfast:StrictAtFast (row 11 25) 11 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 25) 11 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 25) 11 25 hvalid hfast

theorem sr11p26:∀ i ∈ List.range 1,StrictCheckAt 11 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 26) 11 26:=by decide +kernel
  have hfast:StrictAtFast (row 11 26) 11 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 26) 11 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 26) 11 26 hvalid hfast

theorem sr11p27:∀ i ∈ List.range 1,StrictCheckAt 11 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 27) 11 27:=by decide +kernel
  have hfast:StrictAtFast (row 11 27) 11 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 27) 11 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 27) 11 27 hvalid hfast

theorem sr11p28:∀ i ∈ List.range 1,StrictCheckAt 11 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 28) 11 28:=by decide +kernel
  have hfast:StrictAtFast (row 11 28) 11 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 28) 11 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 28) 11 28 hvalid hfast

theorem sr11p29:∀ i ∈ List.range 1,StrictCheckAt 11 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 29) 11 29:=by decide +kernel
  have hfast:StrictAtFast (row 11 29) 11 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 29) 11 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 29) 11 29 hvalid hfast

theorem sr11p30:∀ i ∈ List.range 1,StrictCheckAt 11 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 30) 11 30:=by decide +kernel
  have hfast:StrictAtFast (row 11 30) 11 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 30) 11 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 30) 11 30 hvalid hfast

theorem sr11p31:∀ i ∈ List.range 1,StrictCheckAt 11 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 31) 11 31:=by decide +kernel
  have hfast:StrictAtFast (row 11 31) 11 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 31) 11 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 31) 11 31 hvalid hfast

theorem sr11p32:∀ i ∈ List.range 1,StrictCheckAt 11 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 32) 11 32:=by decide +kernel
  have hfast:StrictAtFast (row 11 32) 11 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 32) 11 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 32) 11 32 hvalid hfast

theorem sr11p33:∀ i ∈ List.range 1,StrictCheckAt 11 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 33) 11 33:=by decide +kernel
  have hfast:StrictAtFast (row 11 33) 11 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 33) 11 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 33) 11 33 hvalid hfast

theorem sr11p34:∀ i ∈ List.range 1,StrictCheckAt 11 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 34) 11 34:=by decide +kernel
  have hfast:StrictAtFast (row 11 34) 11 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 34) 11 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 34) 11 34 hvalid hfast

theorem sr11p35:∀ i ∈ List.range 1,StrictCheckAt 11 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 35) 11 35:=by decide +kernel
  have hfast:StrictAtFast (row 11 35) 11 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 35) 11 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 35) 11 35 hvalid hfast

theorem sr11p36:∀ i ∈ List.range 1,StrictCheckAt 11 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 36) 11 36:=by decide +kernel
  have hfast:StrictAtFast (row 11 36) 11 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 36) 11 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 36) 11 36 hvalid hfast

theorem sr11p37:∀ i ∈ List.range 1,StrictCheckAt 11 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 37) 11 37:=by decide +kernel
  have hfast:StrictAtFast (row 11 37) 11 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 37) 11 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 37) 11 37 hvalid hfast

theorem sr11p38:∀ i ∈ List.range 1,StrictCheckAt 11 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 38) 11 38:=by decide +kernel
  have hfast:StrictAtFast (row 11 38) 11 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 38) 11 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 38) 11 38 hvalid hfast

theorem sr11p39:∀ i ∈ List.range 1,StrictCheckAt 11 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 39) 11 39:=by decide +kernel
  have hfast:StrictAtFast (row 11 39) 11 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 39) 11 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 39) 11 39 hvalid hfast

theorem sr11p40:∀ i ∈ List.range 1,StrictCheckAt 11 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 40) 11 40:=by decide +kernel
  have hfast:StrictAtFast (row 11 40) 11 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 40) 11 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 40) 11 40 hvalid hfast

theorem sr11p41:∀ i ∈ List.range 1,StrictCheckAt 11 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 41) 11 41:=by decide +kernel
  have hfast:StrictAtFast (row 11 41) 11 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 41) 11 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 41) 11 41 hvalid hfast

theorem sr11p42:∀ i ∈ List.range 1,StrictCheckAt 11 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 42) 11 42:=by decide +kernel
  have hfast:StrictAtFast (row 11 42) 11 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 42) 11 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 42) 11 42 hvalid hfast

theorem sr11p43:∀ i ∈ List.range 1,StrictCheckAt 11 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 43) 11 43:=by decide +kernel
  have hfast:StrictAtFast (row 11 43) 11 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 43) 11 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 43) 11 43 hvalid hfast

theorem sr11p44:∀ i ∈ List.range 1,StrictCheckAt 11 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 44) 11 44:=by decide +kernel
  have hfast:StrictAtFast (row 11 44) 11 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 44) 11 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 44) 11 44 hvalid hfast

theorem sr11p45:∀ i ∈ List.range 1,StrictCheckAt 11 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 45) 11 45:=by decide +kernel
  have hfast:StrictAtFast (row 11 45) 11 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 45) 11 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 45) 11 45 hvalid hfast

theorem sr11p46:∀ i ∈ List.range 1,StrictCheckAt 11 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 46) 11 46:=by decide +kernel
  have hfast:StrictAtFast (row 11 46) 11 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 46) 11 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 46) 11 46 hvalid hfast

theorem sr11p47:∀ i ∈ List.range 1,StrictCheckAt 11 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 47) 11 47:=by decide +kernel
  have hfast:StrictAtFast (row 11 47) 11 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 47) 11 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 47) 11 47 hvalid hfast

theorem sr11p48:∀ i ∈ List.range 1,StrictCheckAt 11 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 48) 11 48:=by decide +kernel
  have hfast:StrictAtFast (row 11 48) 11 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 48) 11 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 48) 11 48 hvalid hfast

theorem sr11p49:∀ i ∈ List.range 1,StrictCheckAt 11 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 49) 11 49:=by decide +kernel
  have hfast:StrictAtFast (row 11 49) 11 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 49) 11 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 49) 11 49 hvalid hfast

theorem sr11p50:∀ i ∈ List.range 1,StrictCheckAt 11 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 50) 11 50:=by decide +kernel
  have hfast:StrictAtFast (row 11 50) 11 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 50) 11 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 50) 11 50 hvalid hfast

theorem sr11p51:∀ i ∈ List.range 1,StrictCheckAt 11 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 51) 11 51:=by decide +kernel
  have hfast:StrictAtFast (row 11 51) 11 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 51) 11 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 51) 11 51 hvalid hfast

theorem sr11p52:∀ i ∈ List.range 1,StrictCheckAt 11 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 52) 11 52:=by decide +kernel
  have hfast:StrictAtFast (row 11 52) 11 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 52) 11 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 52) 11 52 hvalid hfast

theorem sr11p53:∀ i ∈ List.range 1,StrictCheckAt 11 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 53) 11 53:=by decide +kernel
  have hfast:StrictAtFast (row 11 53) 11 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 53) 11 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 53) 11 53 hvalid hfast

theorem sr11p54:∀ i ∈ List.range 1,StrictCheckAt 11 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 54) 11 54:=by decide +kernel
  have hfast:StrictAtFast (row 11 54) 11 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 54) 11 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 54) 11 54 hvalid hfast

theorem sr11p55:∀ i ∈ List.range 1,StrictCheckAt 11 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 55) 11 55:=by decide +kernel
  have hfast:StrictAtFast (row 11 55) 11 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 55) 11 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 55) 11 55 hvalid hfast

theorem sr11p56:∀ i ∈ List.range 1,StrictCheckAt 11 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 56) 11 56:=by decide +kernel
  have hfast:StrictAtFast (row 11 56) 11 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 56) 11 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 56) 11 56 hvalid hfast

theorem sr11p57:∀ i ∈ List.range 1,StrictCheckAt 11 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 57) 11 57:=by decide +kernel
  have hfast:StrictAtFast (row 11 57) 11 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 57) 11 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 57) 11 57 hvalid hfast

theorem sr11p58:∀ i ∈ List.range 1,StrictCheckAt 11 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 58) 11 58:=by decide +kernel
  have hfast:StrictAtFast (row 11 58) 11 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 58) 11 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 58) 11 58 hvalid hfast

theorem sr11p59:∀ i ∈ List.range 1,StrictCheckAt 11 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 59) 11 59:=by decide +kernel
  have hfast:StrictAtFast (row 11 59) 11 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 59) 11 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 59) 11 59 hvalid hfast

theorem sr11p60:∀ i ∈ List.range 1,StrictCheckAt 11 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 60) 11 60:=by decide +kernel
  have hfast:StrictAtFast (row 11 60) 11 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 60) 11 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 60) 11 60 hvalid hfast

theorem sr11p61:∀ i ∈ List.range 1,StrictCheckAt 11 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 61) 11 61:=by decide +kernel
  have hfast:StrictAtFast (row 11 61) 11 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 61) 11 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 61) 11 61 hvalid hfast

theorem sr11p62:∀ i ∈ List.range 1,StrictCheckAt 11 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 62) 11 62:=by decide +kernel
  have hfast:StrictAtFast (row 11 62) 11 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 62) 11 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 62) 11 62 hvalid hfast

theorem sr11p63:∀ i ∈ List.range 1,StrictCheckAt 11 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 63) 11 63:=by decide +kernel
  have hfast:StrictAtFast (row 11 63) 11 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 63) 11 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 63) 11 63 hvalid hfast

theorem sr11p64:∀ i ∈ List.range 1,StrictCheckAt 11 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 64) 11 64:=by decide +kernel
  have hfast:StrictAtFast (row 11 64) 11 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 64) 11 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 64) 11 64 hvalid hfast

theorem sr11p65:∀ i ∈ List.range 1,StrictCheckAt 11 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 65) 11 65:=by decide +kernel
  have hfast:StrictAtFast (row 11 65) 11 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 65) 11 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 65) 11 65 hvalid hfast

theorem sr11p66:∀ i ∈ List.range 1,StrictCheckAt 11 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 66) 11 66:=by decide +kernel
  have hfast:StrictAtFast (row 11 66) 11 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 66) 11 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 66) 11 66 hvalid hfast

theorem sr11p67:∀ i ∈ List.range 1,StrictCheckAt 11 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 67) 11 67:=by decide +kernel
  have hfast:StrictAtFast (row 11 67) 11 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 67) 11 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 67) 11 67 hvalid hfast

theorem sr11p68:∀ i ∈ List.range 1,StrictCheckAt 11 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 68) 11 68:=by decide +kernel
  have hfast:StrictAtFast (row 11 68) 11 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 68) 11 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 68) 11 68 hvalid hfast

theorem sr11p69:∀ i ∈ List.range 1,StrictCheckAt 11 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 69) 11 69:=by decide +kernel
  have hfast:StrictAtFast (row 11 69) 11 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 69) 11 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 69) 11 69 hvalid hfast

theorem sr11p70:∀ i ∈ List.range 1,StrictCheckAt 11 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 70) 11 70:=by decide +kernel
  have hfast:StrictAtFast (row 11 70) 11 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 70) 11 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 70) 11 70 hvalid hfast

theorem sr11p71:∀ i ∈ List.range 1,StrictCheckAt 11 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 71) 11 71:=by decide +kernel
  have hfast:StrictAtFast (row 11 71) 11 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 71) 11 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 71) 11 71 hvalid hfast

theorem sr11p72:∀ i ∈ List.range 1,StrictCheckAt 11 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 72) 11 72:=by decide +kernel
  have hfast:StrictAtFast (row 11 72) 11 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 72) 11 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 72) 11 72 hvalid hfast

theorem sr11p73:∀ i ∈ List.range 1,StrictCheckAt 11 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 73) 11 73:=by decide +kernel
  have hfast:StrictAtFast (row 11 73) 11 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 73) 11 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 73) 11 73 hvalid hfast

theorem sr11p74:∀ i ∈ List.range 1,StrictCheckAt 11 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 74) 11 74:=by decide +kernel
  have hfast:StrictAtFast (row 11 74) 11 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 74) 11 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 74) 11 74 hvalid hfast

theorem sr11p75:∀ i ∈ List.range 1,StrictCheckAt 11 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 75) 11 75:=by decide +kernel
  have hfast:StrictAtFast (row 11 75) 11 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 75) 11 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 75) 11 75 hvalid hfast

theorem sr11p76:∀ i ∈ List.range 1,StrictCheckAt 11 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 76) 11 76:=by decide +kernel
  have hfast:StrictAtFast (row 11 76) 11 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 76) 11 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 76) 11 76 hvalid hfast

theorem sr11p77:∀ i ∈ List.range 1,StrictCheckAt 11 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 77) 11 77:=by decide +kernel
  have hfast:StrictAtFast (row 11 77) 11 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 77) 11 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 77) 11 77 hvalid hfast

theorem sr11p78:∀ i ∈ List.range 1,StrictCheckAt 11 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 78) 11 78:=by decide +kernel
  have hfast:StrictAtFast (row 11 78) 11 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 78) 11 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 78) 11 78 hvalid hfast

theorem sr11p79:∀ i ∈ List.range 1,StrictCheckAt 11 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 79) 11 79:=by decide +kernel
  have hfast:StrictAtFast (row 11 79) 11 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 79) 11 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 79) 11 79 hvalid hfast

theorem sr11p80:∀ i ∈ List.range 1,StrictCheckAt 11 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 80) 11 80:=by decide +kernel
  have hfast:StrictAtFast (row 11 80) 11 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 80) 11 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 80) 11 80 hvalid hfast

theorem sr11p81:∀ i ∈ List.range 1,StrictCheckAt 11 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 81) 11 81:=by decide +kernel
  have hfast:StrictAtFast (row 11 81) 11 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 81) 11 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 81) 11 81 hvalid hfast

theorem sr11p82:∀ i ∈ List.range 1,StrictCheckAt 11 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 82) 11 82:=by decide +kernel
  have hfast:StrictAtFast (row 11 82) 11 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 82) 11 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 82) 11 82 hvalid hfast

theorem sr11p83:∀ i ∈ List.range 1,StrictCheckAt 11 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 83) 11 83:=by decide +kernel
  have hfast:StrictAtFast (row 11 83) 11 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 83) 11 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 83) 11 83 hvalid hfast

theorem sr11p84:∀ i ∈ List.range 1,StrictCheckAt 11 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 84) 11 84:=by decide +kernel
  have hfast:StrictAtFast (row 11 84) 11 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 84) 11 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 84) 11 84 hvalid hfast

theorem sr11p85:∀ i ∈ List.range 1,StrictCheckAt 11 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 85) 11 85:=by decide +kernel
  have hfast:StrictAtFast (row 11 85) 11 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 85) 11 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 85) 11 85 hvalid hfast

theorem sr11p86:∀ i ∈ List.range 1,StrictCheckAt 11 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 86) 11 86:=by decide +kernel
  have hfast:StrictAtFast (row 11 86) 11 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 86) 11 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 86) 11 86 hvalid hfast

theorem sr11p87:∀ i ∈ List.range 1,StrictCheckAt 11 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 87) 11 87:=by decide +kernel
  have hfast:StrictAtFast (row 11 87) 11 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 87) 11 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 87) 11 87 hvalid hfast

theorem sr11p88:∀ i ∈ List.range 1,StrictCheckAt 11 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 88) 11 88:=by decide +kernel
  have hfast:StrictAtFast (row 11 88) 11 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 88) 11 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 88) 11 88 hvalid hfast

theorem sr11p89:∀ i ∈ List.range 1,StrictCheckAt 11 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 89) 11 89:=by decide +kernel
  have hfast:StrictAtFast (row 11 89) 11 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 89) 11 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 89) 11 89 hvalid hfast

theorem sr11p90:∀ i ∈ List.range 1,StrictCheckAt 11 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 90) 11 90:=by decide +kernel
  have hfast:StrictAtFast (row 11 90) 11 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 90) 11 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 90) 11 90 hvalid hfast

theorem sr11p91:∀ i ∈ List.range 1,StrictCheckAt 11 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 91) 11 91:=by decide +kernel
  have hfast:StrictAtFast (row 11 91) 11 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 91) 11 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 91) 11 91 hvalid hfast

theorem sr11p92:∀ i ∈ List.range 1,StrictCheckAt 11 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 92) 11 92:=by decide +kernel
  have hfast:StrictAtFast (row 11 92) 11 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 92) 11 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 92) 11 92 hvalid hfast

theorem sr11p93:∀ i ∈ List.range 1,StrictCheckAt 11 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 93) 11 93:=by decide +kernel
  have hfast:StrictAtFast (row 11 93) 11 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 93) 11 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 93) 11 93 hvalid hfast

theorem sr11p94:∀ i ∈ List.range 1,StrictCheckAt 11 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 94) 11 94:=by decide +kernel
  have hfast:StrictAtFast (row 11 94) 11 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 94) 11 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 94) 11 94 hvalid hfast

theorem sr11p95:∀ i ∈ List.range 1,StrictCheckAt 11 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 95) 11 95:=by decide +kernel
  have hfast:StrictAtFast (row 11 95) 11 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 95) 11 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 95) 11 95 hvalid hfast

theorem sr11p96:∀ i ∈ List.range 1,StrictCheckAt 11 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 96) 11 96:=by decide +kernel
  have hfast:StrictAtFast (row 11 96) 11 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 96) 11 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 96) 11 96 hvalid hfast

theorem sr11p97:∀ i ∈ List.range 1,StrictCheckAt 11 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 97) 11 97:=by decide +kernel
  have hfast:StrictAtFast (row 11 97) 11 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 97) 11 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 97) 11 97 hvalid hfast

theorem sr11p98:∀ i ∈ List.range 1,StrictCheckAt 11 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 98) 11 98:=by decide +kernel
  have hfast:StrictAtFast (row 11 98) 11 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 98) 11 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 98) 11 98 hvalid hfast

theorem sr11p99:∀ i ∈ List.range 1,StrictCheckAt 11 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 99) 11 99:=by decide +kernel
  have hfast:StrictAtFast (row 11 99) 11 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 99) 11 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 99) 11 99 hvalid hfast

theorem sr11p100:∀ i ∈ List.range 1,StrictCheckAt 11 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 100) 11 100:=by decide +kernel
  have hfast:StrictAtFast (row 11 100) 11 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 100) 11 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 100) 11 100 hvalid hfast

theorem sr11p101:∀ i ∈ List.range 1,StrictCheckAt 11 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 101) 11 101:=by decide +kernel
  have hfast:StrictAtFast (row 11 101) 11 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 101) 11 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 101) 11 101 hvalid hfast

theorem sr11p102:∀ i ∈ List.range 1,StrictCheckAt 11 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 102) 11 102:=by decide +kernel
  have hfast:StrictAtFast (row 11 102) 11 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 102) 11 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 102) 11 102 hvalid hfast

theorem sr11p103:∀ i ∈ List.range 1,StrictCheckAt 11 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 103) 11 103:=by decide +kernel
  have hfast:StrictAtFast (row 11 103) 11 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 103) 11 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 103) 11 103 hvalid hfast

theorem sr11p104:∀ i ∈ List.range 1,StrictCheckAt 11 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 104) 11 104:=by decide +kernel
  have hfast:StrictAtFast (row 11 104) 11 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 104) 11 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 104) 11 104 hvalid hfast

theorem sr11p105:∀ i ∈ List.range 1,StrictCheckAt 11 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 105) 11 105:=by decide +kernel
  have hfast:StrictAtFast (row 11 105) 11 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 105) 11 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 105) 11 105 hvalid hfast

theorem sr11p106:∀ i ∈ List.range 1,StrictCheckAt 11 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 106) 11 106:=by decide +kernel
  have hfast:StrictAtFast (row 11 106) 11 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 106) 11 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 106) 11 106 hvalid hfast

theorem sr11p107:∀ i ∈ List.range 1,StrictCheckAt 11 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 107) 11 107:=by decide +kernel
  have hfast:StrictAtFast (row 11 107) 11 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 107) 11 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 107) 11 107 hvalid hfast

theorem sr11p108:∀ i ∈ List.range 1,StrictCheckAt 11 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 108) 11 108:=by decide +kernel
  have hfast:StrictAtFast (row 11 108) 11 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 108) 11 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 108) 11 108 hvalid hfast

theorem sr11p109:∀ i ∈ List.range 1,StrictCheckAt 11 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 109) 11 109:=by decide +kernel
  have hfast:StrictAtFast (row 11 109) 11 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 109) 11 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 109) 11 109 hvalid hfast

theorem sr11p110:∀ i ∈ List.range 1,StrictCheckAt 11 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 110) 11 110:=by decide +kernel
  have hfast:StrictAtFast (row 11 110) 11 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 110) 11 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 110) 11 110 hvalid hfast

theorem sr11p111:∀ i ∈ List.range 1,StrictCheckAt 11 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 111) 11 111:=by decide +kernel
  have hfast:StrictAtFast (row 11 111) 11 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 111) 11 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 111) 11 111 hvalid hfast

theorem sr11p112:∀ i ∈ List.range 1,StrictCheckAt 11 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 112) 11 112:=by decide +kernel
  have hfast:StrictAtFast (row 11 112) 11 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 112) 11 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 112) 11 112 hvalid hfast

theorem sr11p113:∀ i ∈ List.range 1,StrictCheckAt 11 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 113) 11 113:=by decide +kernel
  have hfast:StrictAtFast (row 11 113) 11 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 113) 11 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 113) 11 113 hvalid hfast

theorem sr11p114:∀ i ∈ List.range 1,StrictCheckAt 11 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 114) 11 114:=by decide +kernel
  have hfast:StrictAtFast (row 11 114) 11 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 114) 11 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 114) 11 114 hvalid hfast

theorem sr11p115:∀ i ∈ List.range 1,StrictCheckAt 11 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 115) 11 115:=by decide +kernel
  have hfast:StrictAtFast (row 11 115) 11 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 115) 11 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 115) 11 115 hvalid hfast

theorem sr11p116:∀ i ∈ List.range 1,StrictCheckAt 11 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 116) 11 116:=by decide +kernel
  have hfast:StrictAtFast (row 11 116) 11 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 116) 11 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 116) 11 116 hvalid hfast

theorem sr11p117:∀ i ∈ List.range 1,StrictCheckAt 11 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 117) 11 117:=by decide +kernel
  have hfast:StrictAtFast (row 11 117) 11 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 117) 11 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 117) 11 117 hvalid hfast

theorem sr11p118:∀ i ∈ List.range 1,StrictCheckAt 11 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 118) 11 118:=by decide +kernel
  have hfast:StrictAtFast (row 11 118) 11 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 118) 11 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 118) 11 118 hvalid hfast

theorem sr11p119:∀ i ∈ List.range 1,StrictCheckAt 11 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 119) 11 119:=by decide +kernel
  have hfast:StrictAtFast (row 11 119) 11 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 119) 11 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 119) 11 119 hvalid hfast

theorem sr11p120:∀ i ∈ List.range 1,StrictCheckAt 11 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 120) 11 120:=by decide +kernel
  have hfast:StrictAtFast (row 11 120) 11 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 120) 11 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 120) 11 120 hvalid hfast

theorem sr11p121:∀ i ∈ List.range 1,StrictCheckAt 11 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 121) 11 121:=by decide +kernel
  have hfast:StrictAtFast (row 11 121) 11 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 121) 11 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 121) 11 121 hvalid hfast

theorem sr11p122:∀ i ∈ List.range 1,StrictCheckAt 11 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 122) 11 122:=by decide +kernel
  have hfast:StrictAtFast (row 11 122) 11 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 122) 11 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 122) 11 122 hvalid hfast

theorem sr11p123:∀ i ∈ List.range 1,StrictCheckAt 11 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 123) 11 123:=by decide +kernel
  have hfast:StrictAtFast (row 11 123) 11 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 123) 11 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 123) 11 123 hvalid hfast

theorem sr11p124:∀ i ∈ List.range 1,StrictCheckAt 11 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 124) 11 124:=by decide +kernel
  have hfast:StrictAtFast (row 11 124) 11 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 124) 11 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 124) 11 124 hvalid hfast

theorem sr11p125:∀ i ∈ List.range 1,StrictCheckAt 11 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 125) 11 125:=by decide +kernel
  have hfast:StrictAtFast (row 11 125) 11 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 125) 11 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 125) 11 125 hvalid hfast

theorem sr11p126:∀ i ∈ List.range 1,StrictCheckAt 11 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 126) 11 126:=by decide +kernel
  have hfast:StrictAtFast (row 11 126) 11 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 126) 11 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 126) 11 126 hvalid hfast

theorem sr11p127:∀ i ∈ List.range 1,StrictCheckAt 11 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 127) 11 127:=by decide +kernel
  have hfast:StrictAtFast (row 11 127) 11 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 127) 11 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 127) 11 127 hvalid hfast

theorem sr11p128:∀ i ∈ List.range 1,StrictCheckAt 11 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 128) 11 128:=by decide +kernel
  have hfast:StrictAtFast (row 11 128) 11 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 128) 11 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 128) 11 128 hvalid hfast

theorem sr11p129:∀ i ∈ List.range 1,StrictCheckAt 11 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 129) 11 129:=by decide +kernel
  have hfast:StrictAtFast (row 11 129) 11 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 129) 11 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 129) 11 129 hvalid hfast

theorem sr11p130:∀ i ∈ List.range 1,StrictCheckAt 11 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 130) 11 130:=by decide +kernel
  have hfast:StrictAtFast (row 11 130) 11 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 130) 11 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 130) 11 130 hvalid hfast

theorem sr11p131:∀ i ∈ List.range 1,StrictCheckAt 11 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 11 131 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 11 131) 11 131:=by decide +kernel
  have hfast:StrictAtFast (row 11 131) 11 131:=
    BoundaryTailStrictConvex.endpoints_sound (row 11 131) 11 131 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 11 131) 11 131 hvalid hfast

theorem br11p0:∀ i ∈ List.range 4,BaseCheckAt 11 (0+i):=by decide +kernel

theorem br11p1:∀ i ∈ List.range 4,BaseCheckAt 11 (4+i):=by decide +kernel

theorem br11p2:∀ i ∈ List.range 4,BaseCheckAt 11 (8+i):=by decide +kernel

theorem br11p3:∀ i ∈ List.range 4,BaseCheckAt 11 (12+i):=by decide +kernel

theorem br11p4:∀ i ∈ List.range 4,BaseCheckAt 11 (16+i):=by decide +kernel

theorem br11p5:∀ i ∈ List.range 4,BaseCheckAt 11 (20+i):=by decide +kernel

theorem br11p6:∀ i ∈ List.range 4,BaseCheckAt 11 (24+i):=by decide +kernel

theorem br11p7:∀ i ∈ List.range 4,BaseCheckAt 11 (28+i):=by decide +kernel

theorem br11p8:∀ i ∈ List.range 4,BaseCheckAt 11 (32+i):=by decide +kernel

theorem br11p9:∀ i ∈ List.range 4,BaseCheckAt 11 (36+i):=by decide +kernel

theorem br11p10:∀ i ∈ List.range 4,BaseCheckAt 11 (40+i):=by decide +kernel

theorem br11p11:∀ i ∈ List.range 4,BaseCheckAt 11 (44+i):=by decide +kernel

theorem br11p12:∀ i ∈ List.range 4,BaseCheckAt 11 (48+i):=by decide +kernel

theorem br11p13:∀ i ∈ List.range 4,BaseCheckAt 11 (52+i):=by decide +kernel

theorem br11p14:∀ i ∈ List.range 4,BaseCheckAt 11 (56+i):=by decide +kernel

theorem br11p15:∀ i ∈ List.range 4,BaseCheckAt 11 (60+i):=by decide +kernel



theorem br11p16:∀ i ∈ List.range 4,BaseCheckAt 11 (64+i):=by decide +kernel

theorem br11p17:∀ i ∈ List.range 4,BaseCheckAt 11 (68+i):=by decide +kernel

theorem br11p18:∀ i ∈ List.range 4,BaseCheckAt 11 (72+i):=by decide +kernel

theorem br11p19:∀ i ∈ List.range 4,BaseCheckAt 11 (76+i):=by decide +kernel

theorem br11p20:∀ i ∈ List.range 4,BaseCheckAt 11 (80+i):=by decide +kernel

theorem br11p21:∀ i ∈ List.range 4,BaseCheckAt 11 (84+i):=by decide +kernel

theorem br11p22:∀ i ∈ List.range 4,BaseCheckAt 11 (88+i):=by decide +kernel

theorem br11p23:∀ i ∈ List.range 4,BaseCheckAt 11 (92+i):=by decide +kernel

theorem br11p24:∀ i ∈ List.range 4,BaseCheckAt 11 (96+i):=by decide +kernel

theorem br11p25:∀ i ∈ List.range 4,BaseCheckAt 11 (100+i):=by decide +kernel

theorem br11p26:∀ i ∈ List.range 4,BaseCheckAt 11 (104+i):=by decide +kernel

theorem br11p27:∀ i ∈ List.range 4,BaseCheckAt 11 (108+i):=by decide +kernel

theorem br11p28:∀ i ∈ List.range 4,BaseCheckAt 11 (112+i):=by decide +kernel

theorem br11p29:∀ i ∈ List.range 4,BaseCheckAt 11 (116+i):=by decide +kernel

theorem br11p30:∀ i ∈ List.range 4,BaseCheckAt 11 (120+i):=by decide +kernel

theorem br11p31:∀ i ∈ List.range 4,BaseCheckAt 11 (124+i):=by decide +kernel



theorem br11p32:∀ i ∈ List.range 4,BaseCheckAt 11 (128+i):=by decide +kernel



theorem cr11:∀ V ∈ List.range 132,CorrectAt 11 V:=by
  intro V hV
  have hv:V < 132:=List.mem_range.mp hV
  by_cases h0_17:V < 64
  · by_cases h0_8:V < 32
    · by_cases h0_4:V < 16
      · by_cases h0_2:V < 8
        · have h:=cr11p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · have h:=cr11p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h2_4:V < 24
        · have h:=cr11p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · have h:=cr11p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h4_8:V < 48
      · by_cases h4_6:V < 40
        · have h:=cr11p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · have h:=cr11p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h6_8:V < 56
        · have h:=cr11p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · have h:=cr11p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h8_17:V < 96
    · by_cases h8_12:V < 80
      · by_cases h8_10:V < 72
        · have h:=cr11p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
        · have h:=cr11p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
      · by_cases h10_12:V < 88
        · have h:=cr11p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · have h:=cr11p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h12_17:V < 112
      · by_cases h12_14:V < 104
        · have h:=cr11p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
        · have h:=cr11p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
      · by_cases h14_17:V < 120
        · have h:=cr11p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
        · by_cases h15_17:V < 128
          · have h:=cr11p15 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · have h:=cr11p16 (V-128) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

theorem zr11:∀ V ∈ List.range 132,ZeroCheckAt 11 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 11 V (by omega) (by omega) (by omega)
theorem sr11:∀ V ∈ List.range 132,StrictCheckAt 11 V:=by
  intro V hV
  have hv:V < 132:=List.mem_range.mp hV
  by_cases h0_132:V < 66
  · by_cases h0_66:V < 33
    · by_cases h0_33:V < 16
      · by_cases h0_16:V < 8
        · by_cases h0_8:V < 4
          · by_cases h0_4:V < 2
            · by_cases h0_2:V < 1
              · have h:=sr11p0 (V-0) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
              · have h:=sr11p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
            · by_cases h2_4:V < 3
              · have h:=sr11p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
              · have h:=sr11p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
          · by_cases h4_8:V < 6
            · by_cases h4_6:V < 5
              · have h:=sr11p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
              · have h:=sr11p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
            · by_cases h6_8:V < 7
              · have h:=sr11p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
              · have h:=sr11p7 (V-7) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
        · by_cases h8_16:V < 12
          · by_cases h8_12:V < 10
            · by_cases h8_10:V < 9
              · have h:=sr11p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr11p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
            · by_cases h10_12:V < 11
              · have h:=sr11p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr11p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
          · by_cases h12_16:V < 14
            · by_cases h12_14:V < 13
              · have h:=sr11p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr11p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
            · by_cases h14_16:V < 15
              · have h:=sr11p14 (V-14) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
              · have h:=sr11p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
      · by_cases h16_33:V < 24
        · by_cases h16_24:V < 20
          · by_cases h16_20:V < 18
            · by_cases h16_18:V < 17
              · have h:=sr11p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
              · have h:=sr11p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
            · by_cases h18_20:V < 19
              · have h:=sr11p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
              · have h:=sr11p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
          · by_cases h20_24:V < 22
            · by_cases h20_22:V < 21
              · have h:=sr11p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
              · have h:=sr11p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
            · by_cases h22_24:V < 23
              · have h:=sr11p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
              · have h:=sr11p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
        · by_cases h24_33:V < 28
          · by_cases h24_28:V < 26
            · by_cases h24_26:V < 25
              · have h:=sr11p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
              · have h:=sr11p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
            · by_cases h26_28:V < 27
              · have h:=sr11p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
              · have h:=sr11p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
          · by_cases h28_33:V < 30
            · by_cases h28_30:V < 29
              · have h:=sr11p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
              · have h:=sr11p29 (V-29) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_33:V < 31
              · have h:=sr11p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · by_cases h31_33:V < 32
                · have h:=sr11p31 (V-31) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
                · have h:=sr11p32 (V-32) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
    · by_cases h33_66:V < 49
      · by_cases h33_49:V < 41
        · by_cases h33_41:V < 37
          · by_cases h33_37:V < 35
            · by_cases h33_35:V < 34
              · have h:=sr11p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
              · have h:=sr11p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
            · by_cases h35_37:V < 36
              · have h:=sr11p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
              · have h:=sr11p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · by_cases h37_41:V < 39
            · by_cases h37_39:V < 38
              · have h:=sr11p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
              · have h:=sr11p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
            · by_cases h39_41:V < 40
              · have h:=sr11p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
              · have h:=sr11p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · by_cases h41_49:V < 45
          · by_cases h41_45:V < 43
            · by_cases h41_43:V < 42
              · have h:=sr11p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
              · have h:=sr11p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
            · by_cases h43_45:V < 44
              · have h:=sr11p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
              · have h:=sr11p44 (V-44) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · by_cases h45_49:V < 47
            · by_cases h45_47:V < 46
              · have h:=sr11p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr11p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
            · by_cases h47_49:V < 48
              · have h:=sr11p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr11p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
      · by_cases h49_66:V < 57
        · by_cases h49_57:V < 53
          · by_cases h49_53:V < 51
            · by_cases h49_51:V < 50
              · have h:=sr11p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr11p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
            · by_cases h51_53:V < 52
              · have h:=sr11p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr11p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · by_cases h53_57:V < 55
            · by_cases h53_55:V < 54
              · have h:=sr11p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr11p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
            · by_cases h55_57:V < 56
              · have h:=sr11p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr11p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · by_cases h57_66:V < 61
          · by_cases h57_61:V < 59
            · by_cases h57_59:V < 58
              · have h:=sr11p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr11p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
            · by_cases h59_61:V < 60
              · have h:=sr11p59 (V-59) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
              · have h:=sr11p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
          · by_cases h61_66:V < 63
            · by_cases h61_63:V < 62
              · have h:=sr11p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
              · have h:=sr11p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
            · by_cases h63_66:V < 64
              · have h:=sr11p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
              · by_cases h64_66:V < 65
                · have h:=sr11p64 (V-64) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
                · have h:=sr11p65 (V-65) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
  · by_cases h66_132:V < 99
    · by_cases h66_99:V < 82
      · by_cases h66_82:V < 74
        · by_cases h66_74:V < 70
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have h:=sr11p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr11p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
            · by_cases h68_70:V < 69
              · have h:=sr11p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr11p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have h:=sr11p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr11p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
            · by_cases h72_74:V < 73
              · have h:=sr11p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr11p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
        · by_cases h74_82:V < 78
          · by_cases h74_78:V < 76
            · by_cases h74_76:V < 75
              · have h:=sr11p74 (V-74) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
              · have h:=sr11p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
            · by_cases h76_78:V < 77
              · have h:=sr11p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
              · have h:=sr11p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
          · by_cases h78_82:V < 80
            · by_cases h78_80:V < 79
              · have h:=sr11p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
              · have h:=sr11p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
            · by_cases h80_82:V < 81
              · have h:=sr11p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
              · have h:=sr11p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
      · by_cases h82_99:V < 90
        · by_cases h82_90:V < 86
          · by_cases h82_86:V < 84
            · by_cases h82_84:V < 83
              · have h:=sr11p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
              · have h:=sr11p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
            · by_cases h84_86:V < 85
              · have h:=sr11p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
              · have h:=sr11p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
          · by_cases h86_90:V < 88
            · by_cases h86_88:V < 87
              · have h:=sr11p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
              · have h:=sr11p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
            · by_cases h88_90:V < 89
              · have h:=sr11p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
              · have h:=sr11p89 (V-89) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
        · by_cases h90_99:V < 94
          · by_cases h90_94:V < 92
            · by_cases h90_92:V < 91
              · have h:=sr11p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr11p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
            · by_cases h92_94:V < 93
              · have h:=sr11p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr11p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
          · by_cases h94_99:V < 96
            · by_cases h94_96:V < 95
              · have h:=sr11p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr11p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
            · by_cases h96_99:V < 97
              · have h:=sr11p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · by_cases h97_99:V < 98
                · have h:=sr11p97 (V-97) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
                · have h:=sr11p98 (V-98) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
    · by_cases h99_132:V < 115
      · by_cases h99_115:V < 107
        · by_cases h99_107:V < 103
          · by_cases h99_103:V < 101
            · by_cases h99_101:V < 100
              · have h:=sr11p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
              · have h:=sr11p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
            · by_cases h101_103:V < 102
              · have h:=sr11p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
              · have h:=sr11p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
          · by_cases h103_107:V < 105
            · by_cases h103_105:V < 104
              · have h:=sr11p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
              · have h:=sr11p104 (V-104) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
            · by_cases h105_107:V < 106
              · have h:=sr11p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr11p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
        · by_cases h107_115:V < 111
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have h:=sr11p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr11p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
            · by_cases h109_111:V < 110
              · have h:=sr11p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr11p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have h:=sr11p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr11p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
            · by_cases h113_115:V < 114
              · have h:=sr11p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr11p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
      · by_cases h115_132:V < 123
        · by_cases h115_123:V < 119
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have h:=sr11p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr11p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
            · by_cases h117_119:V < 118
              · have h:=sr11p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
              · have h:=sr11p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h
          · by_cases h119_123:V < 121
            · by_cases h119_121:V < 120
              · have h:=sr11p119 (V-119) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 119 ≤ V by omega)] using h
              · have h:=sr11p120 (V-120) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
            · by_cases h121_123:V < 122
              · have h:=sr11p121 (V-121) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 121 ≤ V by omega)] using h
              · have h:=sr11p122 (V-122) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 122 ≤ V by omega)] using h
        · by_cases h123_132:V < 127
          · by_cases h123_127:V < 125
            · by_cases h123_125:V < 124
              · have h:=sr11p123 (V-123) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 123 ≤ V by omega)] using h
              · have h:=sr11p124 (V-124) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
            · by_cases h125_127:V < 126
              · have h:=sr11p125 (V-125) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 125 ≤ V by omega)] using h
              · have h:=sr11p126 (V-126) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 126 ≤ V by omega)] using h
          · by_cases h127_132:V < 129
            · by_cases h127_129:V < 128
              · have h:=sr11p127 (V-127) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 127 ≤ V by omega)] using h
              · have h:=sr11p128 (V-128) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h
            · by_cases h129_132:V < 130
              · have h:=sr11p129 (V-129) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 129 ≤ V by omega)] using h
              · by_cases h130_132:V < 131
                · have h:=sr11p130 (V-130) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 130 ≤ V by omega)] using h
                · have h:=sr11p131 (V-131) (List.mem_range.mpr (by omega))
                  simpa only [Nat.add_sub_of_le (show 131 ≤ V by omega)] using h

theorem br11:∀ V ∈ List.range 132,BaseCheckAt 11 V:=by
  intro V hV
  have hv:V < 132:=List.mem_range.mp hV
  by_cases h0_33:V < 64
  · by_cases h0_16:V < 32
    · by_cases h0_8:V < 16
      · by_cases h0_4:V < 8
        · by_cases h0_2:V < 4
          · have h:=br11p0 (V-0) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
          · have h:=br11p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
        · by_cases h2_4:V < 12
          · have h:=br11p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
          · have h:=br11p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
      · by_cases h4_8:V < 24
        · by_cases h4_6:V < 20
          · have h:=br11p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · have h:=br11p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h6_8:V < 28
          · have h:=br11p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · have h:=br11p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h8_16:V < 48
      · by_cases h8_12:V < 40
        · by_cases h8_10:V < 36
          · have h:=br11p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
          · have h:=br11p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
        · by_cases h10_12:V < 44
          · have h:=br11p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
          · have h:=br11p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
      · by_cases h12_16:V < 56
        · by_cases h12_14:V < 52
          · have h:=br11p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
          · have h:=br11p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
        · by_cases h14_16:V < 60
          · have h:=br11p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
          · have h:=br11p15 (V-60) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
  · by_cases h16_33:V < 96
    · by_cases h16_24:V < 80
      · by_cases h16_20:V < 72
        · by_cases h16_18:V < 68
          · have h:=br11p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br11p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
        · by_cases h18_20:V < 76
          · have h:=br11p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br11p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
      · by_cases h20_24:V < 88
        · by_cases h20_22:V < 84
          · have h:=br11p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br11p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
        · by_cases h22_24:V < 92
          · have h:=br11p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br11p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
    · by_cases h24_33:V < 112
      · by_cases h24_28:V < 104
        · by_cases h24_26:V < 100
          · have h:=br11p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br11p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
        · by_cases h26_28:V < 108
          · have h:=br11p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br11p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
      · by_cases h28_33:V < 120
        · by_cases h28_30:V < 116
          · have h:=br11p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br11p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
        · by_cases h30_33:V < 124
          · have h:=br11p30 (V-120) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 120 ≤ V by omega)] using h
          · by_cases h31_33:V < 128
            · have h:=br11p31 (V-124) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 124 ≤ V by omega)] using h
            · have h:=br11p32 (V-128) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 128 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
