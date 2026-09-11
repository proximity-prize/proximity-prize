import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
