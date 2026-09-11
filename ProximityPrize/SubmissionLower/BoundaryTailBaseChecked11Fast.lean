import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
