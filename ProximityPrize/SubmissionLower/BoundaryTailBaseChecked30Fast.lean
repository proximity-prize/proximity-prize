import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
