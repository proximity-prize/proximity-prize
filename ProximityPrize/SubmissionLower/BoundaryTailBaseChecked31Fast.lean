import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature


namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr31p0:∀ i ∈ List.range 8,CorrectAt 31 (0+i):=by decide +kernel

theorem cr31p1:∀ i ∈ List.range 8,CorrectAt 31 (8+i):=by decide +kernel

theorem cr31p2:∀ i ∈ List.range 8,CorrectAt 31 (16+i):=by decide +kernel

theorem cr31p3:∀ i ∈ List.range 8,CorrectAt 31 (24+i):=by decide +kernel

theorem cr31p4:∀ i ∈ List.range 8,CorrectAt 31 (32+i):=by decide +kernel

theorem cr31p5:∀ i ∈ List.range 8,CorrectAt 31 (40+i):=by decide +kernel

theorem cr31p6:∀ i ∈ List.range 8,CorrectAt 31 (48+i):=by decide +kernel

theorem cr31p7:∀ i ∈ List.range 8,CorrectAt 31 (56+i):=by decide +kernel

theorem cr31p8:∀ i ∈ List.range 8,CorrectAt 31 (64+i):=by decide +kernel

theorem cr31p9:∀ i ∈ List.range 8,CorrectAt 31 (72+i):=by decide +kernel

theorem cr31p10:∀ i ∈ List.range 8,CorrectAt 31 (80+i):=by decide +kernel

theorem cr31p11:∀ i ∈ List.range 8,CorrectAt 31 (88+i):=by decide +kernel

theorem cr31p12:∀ i ∈ List.range 8,CorrectAt 31 (96+i):=by decide +kernel

theorem cr31p13:∀ i ∈ List.range 8,CorrectAt 31 (104+i):=by decide +kernel

theorem sr31p0:∀ i ∈ List.range 1,StrictCheckAt 31 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 0) 31 0:=by decide +kernel
  have hfast:StrictAtFast (row 31 0) 31 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 0) 31 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 0) 31 0 hvalid hfast

theorem sr31p1:∀ i ∈ List.range 1,StrictCheckAt 31 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 1) 31 1:=by decide +kernel
  have hfast:StrictAtFast (row 31 1) 31 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 1) 31 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 1) 31 1 hvalid hfast

theorem sr31p2:∀ i ∈ List.range 1,StrictCheckAt 31 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 2) 31 2:=by decide +kernel
  have hfast:StrictAtFast (row 31 2) 31 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 2) 31 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 2) 31 2 hvalid hfast

theorem sr31p3:∀ i ∈ List.range 1,StrictCheckAt 31 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 3) 31 3:=by decide +kernel
  have hfast:StrictAtFast (row 31 3) 31 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 3) 31 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 3) 31 3 hvalid hfast

theorem sr31p4:∀ i ∈ List.range 1,StrictCheckAt 31 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 4) 31 4:=by decide +kernel
  have hfast:StrictAtFast (row 31 4) 31 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 4) 31 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 4) 31 4 hvalid hfast

theorem sr31p5:∀ i ∈ List.range 1,StrictCheckAt 31 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 5) 31 5:=by decide +kernel
  have hfast:StrictAtFast (row 31 5) 31 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 5) 31 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 5) 31 5 hvalid hfast

theorem sr31p6:∀ i ∈ List.range 1,StrictCheckAt 31 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 6) 31 6:=by decide +kernel
  have hfast:StrictAtFast (row 31 6) 31 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 6) 31 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 6) 31 6 hvalid hfast

theorem sr31p7:∀ i ∈ List.range 1,StrictCheckAt 31 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 7) 31 7:=by decide +kernel
  have hfast:StrictAtFast (row 31 7) 31 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 7) 31 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 7) 31 7 hvalid hfast

theorem sr31p8:∀ i ∈ List.range 1,StrictCheckAt 31 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 8) 31 8:=by decide +kernel
  have hfast:StrictAtFast (row 31 8) 31 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 8) 31 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 8) 31 8 hvalid hfast

theorem sr31p9:∀ i ∈ List.range 1,StrictCheckAt 31 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 9) 31 9:=by decide +kernel
  have hfast:StrictAtFast (row 31 9) 31 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 9) 31 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 9) 31 9 hvalid hfast

theorem sr31p10:∀ i ∈ List.range 1,StrictCheckAt 31 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 10) 31 10:=by decide +kernel
  have hfast:StrictAtFast (row 31 10) 31 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 10) 31 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 10) 31 10 hvalid hfast

theorem sr31p11:∀ i ∈ List.range 1,StrictCheckAt 31 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 11) 31 11:=by decide +kernel
  have hfast:StrictAtFast (row 31 11) 31 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 11) 31 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 11) 31 11 hvalid hfast

theorem sr31p12:∀ i ∈ List.range 1,StrictCheckAt 31 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 12) 31 12:=by decide +kernel
  have hfast:StrictAtFast (row 31 12) 31 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 12) 31 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 12) 31 12 hvalid hfast

theorem sr31p13:∀ i ∈ List.range 1,StrictCheckAt 31 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 13) 31 13:=by decide +kernel
  have hfast:StrictAtFast (row 31 13) 31 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 13) 31 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 13) 31 13 hvalid hfast

theorem sr31p14:∀ i ∈ List.range 1,StrictCheckAt 31 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 14) 31 14:=by decide +kernel
  have hfast:StrictAtFast (row 31 14) 31 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 14) 31 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 14) 31 14 hvalid hfast

theorem sr31p15:∀ i ∈ List.range 1,StrictCheckAt 31 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 15) 31 15:=by decide +kernel
  have hfast:StrictAtFast (row 31 15) 31 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 15) 31 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 15) 31 15 hvalid hfast

theorem sr31p16:∀ i ∈ List.range 1,StrictCheckAt 31 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 16) 31 16:=by decide +kernel
  have hfast:StrictAtFast (row 31 16) 31 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 16) 31 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 16) 31 16 hvalid hfast

theorem sr31p17:∀ i ∈ List.range 1,StrictCheckAt 31 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 17) 31 17:=by decide +kernel
  have hfast:StrictAtFast (row 31 17) 31 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 17) 31 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 17) 31 17 hvalid hfast

theorem sr31p18:∀ i ∈ List.range 1,StrictCheckAt 31 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 18) 31 18:=by decide +kernel
  have hfast:StrictAtFast (row 31 18) 31 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 18) 31 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 18) 31 18 hvalid hfast

theorem sr31p19:∀ i ∈ List.range 1,StrictCheckAt 31 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 19) 31 19:=by decide +kernel
  have hfast:StrictAtFast (row 31 19) 31 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 19) 31 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 19) 31 19 hvalid hfast

theorem sr31p20:∀ i ∈ List.range 1,StrictCheckAt 31 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 20) 31 20:=by decide +kernel
  have hfast:StrictAtFast (row 31 20) 31 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 20) 31 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 20) 31 20 hvalid hfast

theorem sr31p21:∀ i ∈ List.range 1,StrictCheckAt 31 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 21) 31 21:=by decide +kernel
  have hfast:StrictAtFast (row 31 21) 31 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 21) 31 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 21) 31 21 hvalid hfast

theorem sr31p22:∀ i ∈ List.range 1,StrictCheckAt 31 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 22) 31 22:=by decide +kernel
  have hfast:StrictAtFast (row 31 22) 31 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 22) 31 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 22) 31 22 hvalid hfast

theorem sr31p23:∀ i ∈ List.range 1,StrictCheckAt 31 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 23) 31 23:=by decide +kernel
  have hfast:StrictAtFast (row 31 23) 31 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 23) 31 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 23) 31 23 hvalid hfast

theorem sr31p24:∀ i ∈ List.range 1,StrictCheckAt 31 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 24) 31 24:=by decide +kernel
  have hfast:StrictAtFast (row 31 24) 31 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 24) 31 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 24) 31 24 hvalid hfast

theorem sr31p25:∀ i ∈ List.range 1,StrictCheckAt 31 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 25) 31 25:=by decide +kernel
  have hfast:StrictAtFast (row 31 25) 31 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 25) 31 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 25) 31 25 hvalid hfast

theorem sr31p26:∀ i ∈ List.range 1,StrictCheckAt 31 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 26) 31 26:=by decide +kernel
  have hfast:StrictAtFast (row 31 26) 31 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 26) 31 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 26) 31 26 hvalid hfast

theorem sr31p27:∀ i ∈ List.range 1,StrictCheckAt 31 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 27) 31 27:=by decide +kernel
  have hfast:StrictAtFast (row 31 27) 31 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 27) 31 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 27) 31 27 hvalid hfast

theorem sr31p28:∀ i ∈ List.range 1,StrictCheckAt 31 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 28) 31 28:=by decide +kernel
  have hfast:StrictAtFast (row 31 28) 31 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 28) 31 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 28) 31 28 hvalid hfast

theorem sr31p29:∀ i ∈ List.range 1,StrictCheckAt 31 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 29) 31 29:=by decide +kernel
  have hfast:StrictAtFast (row 31 29) 31 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 29) 31 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 29) 31 29 hvalid hfast

theorem sr31p30:∀ i ∈ List.range 1,StrictCheckAt 31 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 30) 31 30:=by decide +kernel
  have hfast:StrictAtFast (row 31 30) 31 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 30) 31 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 30) 31 30 hvalid hfast

theorem sr31p31:∀ i ∈ List.range 1,StrictCheckAt 31 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 31) 31 31:=by decide +kernel
  have hfast:StrictAtFast (row 31 31) 31 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 31) 31 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 31) 31 31 hvalid hfast

theorem sr31p32:∀ i ∈ List.range 1,StrictCheckAt 31 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 32) 31 32:=by decide +kernel
  have hfast:StrictAtFast (row 31 32) 31 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 32) 31 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 32) 31 32 hvalid hfast

theorem sr31p33:∀ i ∈ List.range 1,StrictCheckAt 31 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 33) 31 33:=by decide +kernel
  have hfast:StrictAtFast (row 31 33) 31 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 33) 31 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 33) 31 33 hvalid hfast

theorem sr31p34:∀ i ∈ List.range 1,StrictCheckAt 31 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 34) 31 34:=by decide +kernel
  have hfast:StrictAtFast (row 31 34) 31 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 34) 31 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 34) 31 34 hvalid hfast

theorem sr31p35:∀ i ∈ List.range 1,StrictCheckAt 31 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 35) 31 35:=by decide +kernel
  have hfast:StrictAtFast (row 31 35) 31 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 35) 31 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 35) 31 35 hvalid hfast

theorem sr31p36:∀ i ∈ List.range 1,StrictCheckAt 31 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 36) 31 36:=by decide +kernel
  have hfast:StrictAtFast (row 31 36) 31 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 36) 31 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 36) 31 36 hvalid hfast

theorem sr31p37:∀ i ∈ List.range 1,StrictCheckAt 31 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 37) 31 37:=by decide +kernel
  have hfast:StrictAtFast (row 31 37) 31 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 37) 31 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 37) 31 37 hvalid hfast

theorem sr31p38:∀ i ∈ List.range 1,StrictCheckAt 31 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 38) 31 38:=by decide +kernel
  have hfast:StrictAtFast (row 31 38) 31 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 38) 31 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 38) 31 38 hvalid hfast

theorem sr31p39:∀ i ∈ List.range 1,StrictCheckAt 31 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 39) 31 39:=by decide +kernel
  have hfast:StrictAtFast (row 31 39) 31 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 39) 31 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 39) 31 39 hvalid hfast

theorem sr31p40:∀ i ∈ List.range 1,StrictCheckAt 31 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 40) 31 40:=by decide +kernel
  have hfast:StrictAtFast (row 31 40) 31 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 40) 31 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 40) 31 40 hvalid hfast

theorem sr31p41:∀ i ∈ List.range 1,StrictCheckAt 31 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 41) 31 41:=by decide +kernel
  have hfast:StrictAtFast (row 31 41) 31 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 41) 31 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 41) 31 41 hvalid hfast

theorem sr31p42:∀ i ∈ List.range 1,StrictCheckAt 31 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 42) 31 42:=by decide +kernel
  have hfast:StrictAtFast (row 31 42) 31 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 42) 31 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 42) 31 42 hvalid hfast

theorem sr31p43:∀ i ∈ List.range 1,StrictCheckAt 31 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 43) 31 43:=by decide +kernel
  have hfast:StrictAtFast (row 31 43) 31 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 43) 31 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 43) 31 43 hvalid hfast

theorem sr31p44:∀ i ∈ List.range 1,StrictCheckAt 31 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 44) 31 44:=by decide +kernel
  have hfast:StrictAtFast (row 31 44) 31 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 44) 31 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 44) 31 44 hvalid hfast

theorem sr31p45:∀ i ∈ List.range 1,StrictCheckAt 31 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 45) 31 45:=by decide +kernel
  have hfast:StrictAtFast (row 31 45) 31 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 45) 31 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 45) 31 45 hvalid hfast

theorem sr31p46:∀ i ∈ List.range 1,StrictCheckAt 31 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 46) 31 46:=by decide +kernel
  have hfast:StrictAtFast (row 31 46) 31 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 46) 31 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 46) 31 46 hvalid hfast

theorem sr31p47:∀ i ∈ List.range 1,StrictCheckAt 31 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 47) 31 47:=by decide +kernel
  have hfast:StrictAtFast (row 31 47) 31 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 47) 31 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 47) 31 47 hvalid hfast

theorem sr31p48:∀ i ∈ List.range 1,StrictCheckAt 31 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 48) 31 48:=by decide +kernel
  have hfast:StrictAtFast (row 31 48) 31 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 48) 31 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 48) 31 48 hvalid hfast

theorem sr31p49:∀ i ∈ List.range 1,StrictCheckAt 31 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 49) 31 49:=by decide +kernel
  have hfast:StrictAtFast (row 31 49) 31 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 49) 31 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 49) 31 49 hvalid hfast

theorem sr31p50:∀ i ∈ List.range 1,StrictCheckAt 31 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 50) 31 50:=by decide +kernel
  have hfast:StrictAtFast (row 31 50) 31 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 50) 31 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 50) 31 50 hvalid hfast

theorem sr31p51:∀ i ∈ List.range 1,StrictCheckAt 31 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 51) 31 51:=by decide +kernel
  have hfast:StrictAtFast (row 31 51) 31 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 51) 31 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 51) 31 51 hvalid hfast

theorem sr31p52:∀ i ∈ List.range 1,StrictCheckAt 31 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 52) 31 52:=by decide +kernel
  have hfast:StrictAtFast (row 31 52) 31 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 52) 31 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 52) 31 52 hvalid hfast

theorem sr31p53:∀ i ∈ List.range 1,StrictCheckAt 31 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 53) 31 53:=by decide +kernel
  have hfast:StrictAtFast (row 31 53) 31 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 53) 31 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 53) 31 53 hvalid hfast

theorem sr31p54:∀ i ∈ List.range 1,StrictCheckAt 31 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 54) 31 54:=by decide +kernel
  have hfast:StrictAtFast (row 31 54) 31 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 54) 31 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 54) 31 54 hvalid hfast

theorem sr31p55:∀ i ∈ List.range 1,StrictCheckAt 31 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 55) 31 55:=by decide +kernel
  have hfast:StrictAtFast (row 31 55) 31 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 55) 31 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 55) 31 55 hvalid hfast

theorem sr31p56:∀ i ∈ List.range 1,StrictCheckAt 31 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 56) 31 56:=by decide +kernel
  have hfast:StrictAtFast (row 31 56) 31 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 56) 31 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 56) 31 56 hvalid hfast

theorem sr31p57:∀ i ∈ List.range 1,StrictCheckAt 31 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 57) 31 57:=by decide +kernel
  have hfast:StrictAtFast (row 31 57) 31 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 57) 31 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 57) 31 57 hvalid hfast

theorem sr31p58:∀ i ∈ List.range 1,StrictCheckAt 31 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 58) 31 58:=by decide +kernel
  have hfast:StrictAtFast (row 31 58) 31 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 58) 31 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 58) 31 58 hvalid hfast

theorem sr31p59:∀ i ∈ List.range 1,StrictCheckAt 31 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 59) 31 59:=by decide +kernel
  have hfast:StrictAtFast (row 31 59) 31 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 59) 31 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 59) 31 59 hvalid hfast

theorem sr31p60:∀ i ∈ List.range 1,StrictCheckAt 31 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 60) 31 60:=by decide +kernel
  have hfast:StrictAtFast (row 31 60) 31 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 60) 31 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 60) 31 60 hvalid hfast

theorem sr31p61:∀ i ∈ List.range 1,StrictCheckAt 31 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 61) 31 61:=by decide +kernel
  have hfast:StrictAtFast (row 31 61) 31 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 61) 31 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 61) 31 61 hvalid hfast

theorem sr31p62:∀ i ∈ List.range 1,StrictCheckAt 31 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 62) 31 62:=by decide +kernel
  have hfast:StrictAtFast (row 31 62) 31 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 62) 31 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 62) 31 62 hvalid hfast

theorem sr31p63:∀ i ∈ List.range 1,StrictCheckAt 31 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 63) 31 63:=by decide +kernel
  have hfast:StrictAtFast (row 31 63) 31 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 63) 31 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 63) 31 63 hvalid hfast

theorem sr31p64:∀ i ∈ List.range 1,StrictCheckAt 31 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 64) 31 64:=by decide +kernel
  have hfast:StrictAtFast (row 31 64) 31 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 64) 31 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 64) 31 64 hvalid hfast

theorem sr31p65:∀ i ∈ List.range 1,StrictCheckAt 31 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 65) 31 65:=by decide +kernel
  have hfast:StrictAtFast (row 31 65) 31 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 65) 31 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 65) 31 65 hvalid hfast

theorem sr31p66:∀ i ∈ List.range 1,StrictCheckAt 31 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 66) 31 66:=by decide +kernel
  have hfast:StrictAtFast (row 31 66) 31 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 66) 31 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 66) 31 66 hvalid hfast

theorem sr31p67:∀ i ∈ List.range 1,StrictCheckAt 31 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 67) 31 67:=by decide +kernel
  have hfast:StrictAtFast (row 31 67) 31 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 67) 31 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 67) 31 67 hvalid hfast

theorem sr31p68:∀ i ∈ List.range 1,StrictCheckAt 31 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 68) 31 68:=by decide +kernel
  have hfast:StrictAtFast (row 31 68) 31 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 68) 31 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 68) 31 68 hvalid hfast

theorem sr31p69:∀ i ∈ List.range 1,StrictCheckAt 31 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 69) 31 69:=by decide +kernel
  have hfast:StrictAtFast (row 31 69) 31 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 69) 31 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 69) 31 69 hvalid hfast

theorem sr31p70:∀ i ∈ List.range 1,StrictCheckAt 31 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 70) 31 70:=by decide +kernel
  have hfast:StrictAtFast (row 31 70) 31 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 70) 31 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 70) 31 70 hvalid hfast

theorem sr31p71:∀ i ∈ List.range 1,StrictCheckAt 31 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 71) 31 71:=by decide +kernel
  have hfast:StrictAtFast (row 31 71) 31 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 71) 31 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 71) 31 71 hvalid hfast

theorem sr31p72:∀ i ∈ List.range 1,StrictCheckAt 31 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 72) 31 72:=by decide +kernel
  have hfast:StrictAtFast (row 31 72) 31 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 72) 31 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 72) 31 72 hvalid hfast

theorem sr31p73:∀ i ∈ List.range 1,StrictCheckAt 31 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 73) 31 73:=by decide +kernel
  have hfast:StrictAtFast (row 31 73) 31 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 73) 31 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 73) 31 73 hvalid hfast

theorem sr31p74:∀ i ∈ List.range 1,StrictCheckAt 31 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 74) 31 74:=by decide +kernel
  have hfast:StrictAtFast (row 31 74) 31 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 74) 31 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 74) 31 74 hvalid hfast

theorem sr31p75:∀ i ∈ List.range 1,StrictCheckAt 31 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 75) 31 75:=by decide +kernel
  have hfast:StrictAtFast (row 31 75) 31 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 75) 31 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 75) 31 75 hvalid hfast

theorem sr31p76:∀ i ∈ List.range 1,StrictCheckAt 31 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 76) 31 76:=by decide +kernel
  have hfast:StrictAtFast (row 31 76) 31 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 76) 31 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 76) 31 76 hvalid hfast

theorem sr31p77:∀ i ∈ List.range 1,StrictCheckAt 31 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 77) 31 77:=by decide +kernel
  have hfast:StrictAtFast (row 31 77) 31 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 77) 31 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 77) 31 77 hvalid hfast

theorem sr31p78:∀ i ∈ List.range 1,StrictCheckAt 31 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 78) 31 78:=by decide +kernel
  have hfast:StrictAtFast (row 31 78) 31 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 78) 31 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 78) 31 78 hvalid hfast

theorem sr31p79:∀ i ∈ List.range 1,StrictCheckAt 31 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 79) 31 79:=by decide +kernel
  have hfast:StrictAtFast (row 31 79) 31 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 79) 31 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 79) 31 79 hvalid hfast

theorem sr31p80:∀ i ∈ List.range 1,StrictCheckAt 31 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 80) 31 80:=by decide +kernel
  have hfast:StrictAtFast (row 31 80) 31 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 80) 31 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 80) 31 80 hvalid hfast

theorem sr31p81:∀ i ∈ List.range 1,StrictCheckAt 31 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 81) 31 81:=by decide +kernel
  have hfast:StrictAtFast (row 31 81) 31 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 81) 31 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 81) 31 81 hvalid hfast

theorem sr31p82:∀ i ∈ List.range 1,StrictCheckAt 31 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 82) 31 82:=by decide +kernel
  have hfast:StrictAtFast (row 31 82) 31 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 82) 31 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 82) 31 82 hvalid hfast

theorem sr31p83:∀ i ∈ List.range 1,StrictCheckAt 31 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 83) 31 83:=by decide +kernel
  have hfast:StrictAtFast (row 31 83) 31 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 83) 31 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 83) 31 83 hvalid hfast

theorem sr31p84:∀ i ∈ List.range 1,StrictCheckAt 31 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 84) 31 84:=by decide +kernel
  have hfast:StrictAtFast (row 31 84) 31 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 84) 31 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 84) 31 84 hvalid hfast

theorem sr31p85:∀ i ∈ List.range 1,StrictCheckAt 31 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 85) 31 85:=by decide +kernel
  have hfast:StrictAtFast (row 31 85) 31 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 85) 31 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 85) 31 85 hvalid hfast

theorem sr31p86:∀ i ∈ List.range 1,StrictCheckAt 31 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 86) 31 86:=by decide +kernel
  have hfast:StrictAtFast (row 31 86) 31 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 86) 31 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 86) 31 86 hvalid hfast

theorem sr31p87:∀ i ∈ List.range 1,StrictCheckAt 31 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 87) 31 87:=by decide +kernel
  have hfast:StrictAtFast (row 31 87) 31 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 87) 31 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 87) 31 87 hvalid hfast

theorem sr31p88:∀ i ∈ List.range 1,StrictCheckAt 31 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 88) 31 88:=by decide +kernel
  have hfast:StrictAtFast (row 31 88) 31 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 88) 31 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 88) 31 88 hvalid hfast

theorem sr31p89:∀ i ∈ List.range 1,StrictCheckAt 31 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 89) 31 89:=by decide +kernel
  have hfast:StrictAtFast (row 31 89) 31 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 89) 31 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 89) 31 89 hvalid hfast

theorem sr31p90:∀ i ∈ List.range 1,StrictCheckAt 31 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 90) 31 90:=by decide +kernel
  have hfast:StrictAtFast (row 31 90) 31 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 90) 31 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 90) 31 90 hvalid hfast

theorem sr31p91:∀ i ∈ List.range 1,StrictCheckAt 31 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 91) 31 91:=by decide +kernel
  have hfast:StrictAtFast (row 31 91) 31 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 91) 31 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 91) 31 91 hvalid hfast

theorem sr31p92:∀ i ∈ List.range 1,StrictCheckAt 31 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 92) 31 92:=by decide +kernel
  have hfast:StrictAtFast (row 31 92) 31 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 92) 31 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 92) 31 92 hvalid hfast

theorem sr31p93:∀ i ∈ List.range 1,StrictCheckAt 31 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 93) 31 93:=by decide +kernel
  have hfast:StrictAtFast (row 31 93) 31 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 93) 31 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 93) 31 93 hvalid hfast

theorem sr31p94:∀ i ∈ List.range 1,StrictCheckAt 31 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 94) 31 94:=by decide +kernel
  have hfast:StrictAtFast (row 31 94) 31 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 94) 31 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 94) 31 94 hvalid hfast

theorem sr31p95:∀ i ∈ List.range 1,StrictCheckAt 31 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 95) 31 95:=by decide +kernel
  have hfast:StrictAtFast (row 31 95) 31 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 95) 31 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 95) 31 95 hvalid hfast

theorem sr31p96:∀ i ∈ List.range 1,StrictCheckAt 31 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 96) 31 96:=by decide +kernel
  have hfast:StrictAtFast (row 31 96) 31 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 96) 31 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 96) 31 96 hvalid hfast

theorem sr31p97:∀ i ∈ List.range 1,StrictCheckAt 31 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 97) 31 97:=by decide +kernel
  have hfast:StrictAtFast (row 31 97) 31 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 97) 31 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 97) 31 97 hvalid hfast

theorem sr31p98:∀ i ∈ List.range 1,StrictCheckAt 31 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 98) 31 98:=by decide +kernel
  have hfast:StrictAtFast (row 31 98) 31 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 98) 31 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 98) 31 98 hvalid hfast

theorem sr31p99:∀ i ∈ List.range 1,StrictCheckAt 31 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 99) 31 99:=by decide +kernel
  have hfast:StrictAtFast (row 31 99) 31 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 99) 31 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 99) 31 99 hvalid hfast

theorem sr31p100:∀ i ∈ List.range 1,StrictCheckAt 31 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 100) 31 100:=by decide +kernel
  have hfast:StrictAtFast (row 31 100) 31 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 100) 31 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 100) 31 100 hvalid hfast

theorem sr31p101:∀ i ∈ List.range 1,StrictCheckAt 31 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 101) 31 101:=by decide +kernel
  have hfast:StrictAtFast (row 31 101) 31 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 101) 31 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 101) 31 101 hvalid hfast

theorem sr31p102:∀ i ∈ List.range 1,StrictCheckAt 31 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 102) 31 102:=by decide +kernel
  have hfast:StrictAtFast (row 31 102) 31 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 102) 31 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 102) 31 102 hvalid hfast

theorem sr31p103:∀ i ∈ List.range 1,StrictCheckAt 31 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 103) 31 103:=by decide +kernel
  have hfast:StrictAtFast (row 31 103) 31 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 103) 31 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 103) 31 103 hvalid hfast

theorem sr31p104:∀ i ∈ List.range 1,StrictCheckAt 31 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 104) 31 104:=by decide +kernel
  have hfast:StrictAtFast (row 31 104) 31 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 104) 31 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 104) 31 104 hvalid hfast

theorem sr31p105:∀ i ∈ List.range 1,StrictCheckAt 31 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 105) 31 105:=by decide +kernel
  have hfast:StrictAtFast (row 31 105) 31 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 105) 31 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 105) 31 105 hvalid hfast

theorem sr31p106:∀ i ∈ List.range 1,StrictCheckAt 31 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 106) 31 106:=by decide +kernel
  have hfast:StrictAtFast (row 31 106) 31 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 106) 31 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 106) 31 106 hvalid hfast

theorem sr31p107:∀ i ∈ List.range 1,StrictCheckAt 31 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 107) 31 107:=by decide +kernel
  have hfast:StrictAtFast (row 31 107) 31 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 107) 31 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 107) 31 107 hvalid hfast

theorem sr31p108:∀ i ∈ List.range 1,StrictCheckAt 31 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 108) 31 108:=by decide +kernel
  have hfast:StrictAtFast (row 31 108) 31 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 108) 31 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 108) 31 108 hvalid hfast

theorem sr31p109:∀ i ∈ List.range 1,StrictCheckAt 31 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 109) 31 109:=by decide +kernel
  have hfast:StrictAtFast (row 31 109) 31 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 109) 31 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 109) 31 109 hvalid hfast

theorem sr31p110:∀ i ∈ List.range 1,StrictCheckAt 31 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 110) 31 110:=by decide +kernel
  have hfast:StrictAtFast (row 31 110) 31 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 110) 31 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 110) 31 110 hvalid hfast

theorem sr31p111:∀ i ∈ List.range 1,StrictCheckAt 31 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 31 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 31 111) 31 111:=by decide +kernel
  have hfast:StrictAtFast (row 31 111) 31 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 31 111) 31 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 31 111) 31 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
