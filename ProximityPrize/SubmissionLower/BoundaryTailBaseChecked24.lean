import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23
import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr24p0:∀ i ∈ List.range 8,CorrectAt 24 (0+i):=by decide +kernel

theorem cr24p1:∀ i ∈ List.range 8,CorrectAt 24 (8+i):=by decide +kernel

theorem cr24p2:∀ i ∈ List.range 8,CorrectAt 24 (16+i):=by decide +kernel

theorem cr24p3:∀ i ∈ List.range 8,CorrectAt 24 (24+i):=by decide +kernel

theorem cr24p4:∀ i ∈ List.range 8,CorrectAt 24 (32+i):=by decide +kernel

theorem cr24p5:∀ i ∈ List.range 8,CorrectAt 24 (40+i):=by decide +kernel

theorem cr24p6:∀ i ∈ List.range 8,CorrectAt 24 (48+i):=by decide +kernel

theorem cr24p7:∀ i ∈ List.range 8,CorrectAt 24 (56+i):=by decide +kernel

theorem cr24p8:∀ i ∈ List.range 8,CorrectAt 24 (64+i):=by decide +kernel

theorem cr24p9:∀ i ∈ List.range 8,CorrectAt 24 (72+i):=by decide +kernel

theorem cr24p10:∀ i ∈ List.range 8,CorrectAt 24 (80+i):=by decide +kernel

theorem cr24p11:∀ i ∈ List.range 8,CorrectAt 24 (88+i):=by decide +kernel

theorem cr24p12:∀ i ∈ List.range 8,CorrectAt 24 (96+i):=by decide +kernel

theorem cr24p13:∀ i ∈ List.range 8,CorrectAt 24 (104+i):=by decide +kernel

theorem cr24p14:∀ i ∈ List.range 7,CorrectAt 24 (112+i):=by decide +kernel

theorem sr24p0:∀ i ∈ List.range 1,StrictCheckAt 24 (0+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 0 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 0) 24 0:=by decide +kernel
  have hfast:StrictAtFast (row 24 0) 24 0:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 0) 24 0 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 0) 24 0 hvalid hfast

theorem sr24p1:∀ i ∈ List.range 1,StrictCheckAt 24 (1+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 1 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 1) 24 1:=by decide +kernel
  have hfast:StrictAtFast (row 24 1) 24 1:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 1) 24 1 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 1) 24 1 hvalid hfast

theorem sr24p2:∀ i ∈ List.range 1,StrictCheckAt 24 (2+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 2 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 2) 24 2:=by decide +kernel
  have hfast:StrictAtFast (row 24 2) 24 2:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 2) 24 2 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 2) 24 2 hvalid hfast

theorem sr24p3:∀ i ∈ List.range 1,StrictCheckAt 24 (3+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 3 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 3) 24 3:=by decide +kernel
  have hfast:StrictAtFast (row 24 3) 24 3:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 3) 24 3 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 3) 24 3 hvalid hfast

theorem sr24p4:∀ i ∈ List.range 1,StrictCheckAt 24 (4+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 4 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 4) 24 4:=by decide +kernel
  have hfast:StrictAtFast (row 24 4) 24 4:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 4) 24 4 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 4) 24 4 hvalid hfast

theorem sr24p5:∀ i ∈ List.range 1,StrictCheckAt 24 (5+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 5 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 5) 24 5:=by decide +kernel
  have hfast:StrictAtFast (row 24 5) 24 5:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 5) 24 5 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 5) 24 5 hvalid hfast

theorem sr24p6:∀ i ∈ List.range 1,StrictCheckAt 24 (6+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 6 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 6) 24 6:=by decide +kernel
  have hfast:StrictAtFast (row 24 6) 24 6:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 6) 24 6 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 6) 24 6 hvalid hfast

theorem sr24p7:∀ i ∈ List.range 1,StrictCheckAt 24 (7+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 7 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 7) 24 7:=by decide +kernel
  have hfast:StrictAtFast (row 24 7) 24 7:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 7) 24 7 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 7) 24 7 hvalid hfast

theorem sr24p8:∀ i ∈ List.range 1,StrictCheckAt 24 (8+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 8 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 8) 24 8:=by decide +kernel
  have hfast:StrictAtFast (row 24 8) 24 8:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 8) 24 8 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 8) 24 8 hvalid hfast

theorem sr24p9:∀ i ∈ List.range 1,StrictCheckAt 24 (9+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 9 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 9) 24 9:=by decide +kernel
  have hfast:StrictAtFast (row 24 9) 24 9:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 9) 24 9 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 9) 24 9 hvalid hfast

theorem sr24p10:∀ i ∈ List.range 1,StrictCheckAt 24 (10+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 10 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 10) 24 10:=by decide +kernel
  have hfast:StrictAtFast (row 24 10) 24 10:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 10) 24 10 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 10) 24 10 hvalid hfast

theorem sr24p11:∀ i ∈ List.range 1,StrictCheckAt 24 (11+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 11 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 11) 24 11:=by decide +kernel
  have hfast:StrictAtFast (row 24 11) 24 11:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 11) 24 11 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 11) 24 11 hvalid hfast

theorem sr24p12:∀ i ∈ List.range 1,StrictCheckAt 24 (12+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 12 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 12) 24 12:=by decide +kernel
  have hfast:StrictAtFast (row 24 12) 24 12:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 12) 24 12 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 12) 24 12 hvalid hfast

theorem sr24p13:∀ i ∈ List.range 1,StrictCheckAt 24 (13+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 13 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 13) 24 13:=by decide +kernel
  have hfast:StrictAtFast (row 24 13) 24 13:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 13) 24 13 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 13) 24 13 hvalid hfast

theorem sr24p14:∀ i ∈ List.range 1,StrictCheckAt 24 (14+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 14 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 14) 24 14:=by decide +kernel
  have hfast:StrictAtFast (row 24 14) 24 14:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 14) 24 14 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 14) 24 14 hvalid hfast

theorem sr24p15:∀ i ∈ List.range 1,StrictCheckAt 24 (15+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 15 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 15) 24 15:=by decide +kernel
  have hfast:StrictAtFast (row 24 15) 24 15:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 15) 24 15 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 15) 24 15 hvalid hfast

theorem sr24p16:∀ i ∈ List.range 1,StrictCheckAt 24 (16+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 16 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 16) 24 16:=by decide +kernel
  have hfast:StrictAtFast (row 24 16) 24 16:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 16) 24 16 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 16) 24 16 hvalid hfast

theorem sr24p17:∀ i ∈ List.range 1,StrictCheckAt 24 (17+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 17 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 17) 24 17:=by decide +kernel
  have hfast:StrictAtFast (row 24 17) 24 17:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 17) 24 17 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 17) 24 17 hvalid hfast

theorem sr24p18:∀ i ∈ List.range 1,StrictCheckAt 24 (18+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 18 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 18) 24 18:=by decide +kernel
  have hfast:StrictAtFast (row 24 18) 24 18:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 18) 24 18 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 18) 24 18 hvalid hfast

theorem sr24p19:∀ i ∈ List.range 1,StrictCheckAt 24 (19+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 19 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 19) 24 19:=by decide +kernel
  have hfast:StrictAtFast (row 24 19) 24 19:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 19) 24 19 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 19) 24 19 hvalid hfast

theorem sr24p20:∀ i ∈ List.range 1,StrictCheckAt 24 (20+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 20 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 20) 24 20:=by decide +kernel
  have hfast:StrictAtFast (row 24 20) 24 20:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 20) 24 20 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 20) 24 20 hvalid hfast

theorem sr24p21:∀ i ∈ List.range 1,StrictCheckAt 24 (21+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 21 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 21) 24 21:=by decide +kernel
  have hfast:StrictAtFast (row 24 21) 24 21:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 21) 24 21 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 21) 24 21 hvalid hfast

theorem sr24p22:∀ i ∈ List.range 1,StrictCheckAt 24 (22+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 22 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 22) 24 22:=by decide +kernel
  have hfast:StrictAtFast (row 24 22) 24 22:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 22) 24 22 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 22) 24 22 hvalid hfast

theorem sr24p23:∀ i ∈ List.range 1,StrictCheckAt 24 (23+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 23 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 23) 24 23:=by decide +kernel
  have hfast:StrictAtFast (row 24 23) 24 23:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 23) 24 23 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 23) 24 23 hvalid hfast

theorem sr24p24:∀ i ∈ List.range 1,StrictCheckAt 24 (24+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 24 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 24) 24 24:=by decide +kernel
  have hfast:StrictAtFast (row 24 24) 24 24:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 24) 24 24 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 24) 24 24 hvalid hfast

theorem sr24p25:∀ i ∈ List.range 1,StrictCheckAt 24 (25+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 25 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 25) 24 25:=by decide +kernel
  have hfast:StrictAtFast (row 24 25) 24 25:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 25) 24 25 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 25) 24 25 hvalid hfast

theorem sr24p26:∀ i ∈ List.range 1,StrictCheckAt 24 (26+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 26 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 26) 24 26:=by decide +kernel
  have hfast:StrictAtFast (row 24 26) 24 26:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 26) 24 26 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 26) 24 26 hvalid hfast

theorem sr24p27:∀ i ∈ List.range 1,StrictCheckAt 24 (27+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 27 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 27) 24 27:=by decide +kernel
  have hfast:StrictAtFast (row 24 27) 24 27:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 27) 24 27 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 27) 24 27 hvalid hfast

theorem sr24p28:∀ i ∈ List.range 1,StrictCheckAt 24 (28+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 28 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 28) 24 28:=by decide +kernel
  have hfast:StrictAtFast (row 24 28) 24 28:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 28) 24 28 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 28) 24 28 hvalid hfast

theorem sr24p29:∀ i ∈ List.range 1,StrictCheckAt 24 (29+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 29 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 29) 24 29:=by decide +kernel
  have hfast:StrictAtFast (row 24 29) 24 29:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 29) 24 29 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 29) 24 29 hvalid hfast

theorem sr24p30:∀ i ∈ List.range 1,StrictCheckAt 24 (30+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 30 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 30) 24 30:=by decide +kernel
  have hfast:StrictAtFast (row 24 30) 24 30:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 30) 24 30 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 30) 24 30 hvalid hfast

theorem sr24p31:∀ i ∈ List.range 1,StrictCheckAt 24 (31+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 31 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 31) 24 31:=by decide +kernel
  have hfast:StrictAtFast (row 24 31) 24 31:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 31) 24 31 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 31) 24 31 hvalid hfast

theorem sr24p32:∀ i ∈ List.range 1,StrictCheckAt 24 (32+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 32 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 32) 24 32:=by decide +kernel
  have hfast:StrictAtFast (row 24 32) 24 32:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 32) 24 32 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 32) 24 32 hvalid hfast

theorem sr24p33:∀ i ∈ List.range 1,StrictCheckAt 24 (33+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 33 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 33) 24 33:=by decide +kernel
  have hfast:StrictAtFast (row 24 33) 24 33:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 33) 24 33 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 33) 24 33 hvalid hfast

theorem sr24p34:∀ i ∈ List.range 1,StrictCheckAt 24 (34+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 34 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 34) 24 34:=by decide +kernel
  have hfast:StrictAtFast (row 24 34) 24 34:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 34) 24 34 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 34) 24 34 hvalid hfast

theorem sr24p35:∀ i ∈ List.range 1,StrictCheckAt 24 (35+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 35 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 35) 24 35:=by decide +kernel
  have hfast:StrictAtFast (row 24 35) 24 35:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 35) 24 35 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 35) 24 35 hvalid hfast

theorem sr24p36:∀ i ∈ List.range 1,StrictCheckAt 24 (36+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 36 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 36) 24 36:=by decide +kernel
  have hfast:StrictAtFast (row 24 36) 24 36:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 36) 24 36 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 36) 24 36 hvalid hfast

theorem sr24p37:∀ i ∈ List.range 1,StrictCheckAt 24 (37+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 37 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 37) 24 37:=by decide +kernel
  have hfast:StrictAtFast (row 24 37) 24 37:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 37) 24 37 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 37) 24 37 hvalid hfast

theorem sr24p38:∀ i ∈ List.range 1,StrictCheckAt 24 (38+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 38 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 38) 24 38:=by decide +kernel
  have hfast:StrictAtFast (row 24 38) 24 38:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 38) 24 38 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 38) 24 38 hvalid hfast

theorem sr24p39:∀ i ∈ List.range 1,StrictCheckAt 24 (39+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 39 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 39) 24 39:=by decide +kernel
  have hfast:StrictAtFast (row 24 39) 24 39:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 39) 24 39 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 39) 24 39 hvalid hfast

theorem sr24p40:∀ i ∈ List.range 1,StrictCheckAt 24 (40+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 40 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 40) 24 40:=by decide +kernel
  have hfast:StrictAtFast (row 24 40) 24 40:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 40) 24 40 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 40) 24 40 hvalid hfast

theorem sr24p41:∀ i ∈ List.range 1,StrictCheckAt 24 (41+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 41 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 41) 24 41:=by decide +kernel
  have hfast:StrictAtFast (row 24 41) 24 41:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 41) 24 41 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 41) 24 41 hvalid hfast

theorem sr24p42:∀ i ∈ List.range 1,StrictCheckAt 24 (42+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 42 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 42) 24 42:=by decide +kernel
  have hfast:StrictAtFast (row 24 42) 24 42:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 42) 24 42 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 42) 24 42 hvalid hfast

theorem sr24p43:∀ i ∈ List.range 1,StrictCheckAt 24 (43+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 43 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 43) 24 43:=by decide +kernel
  have hfast:StrictAtFast (row 24 43) 24 43:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 43) 24 43 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 43) 24 43 hvalid hfast

theorem sr24p44:∀ i ∈ List.range 1,StrictCheckAt 24 (44+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 44 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 44) 24 44:=by decide +kernel
  have hfast:StrictAtFast (row 24 44) 24 44:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 44) 24 44 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 44) 24 44 hvalid hfast

theorem sr24p45:∀ i ∈ List.range 1,StrictCheckAt 24 (45+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 45 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 45) 24 45:=by decide +kernel
  have hfast:StrictAtFast (row 24 45) 24 45:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 45) 24 45 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 45) 24 45 hvalid hfast

theorem sr24p46:∀ i ∈ List.range 1,StrictCheckAt 24 (46+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 46 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 46) 24 46:=by decide +kernel
  have hfast:StrictAtFast (row 24 46) 24 46:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 46) 24 46 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 46) 24 46 hvalid hfast

theorem sr24p47:∀ i ∈ List.range 1,StrictCheckAt 24 (47+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 47 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 47) 24 47:=by decide +kernel
  have hfast:StrictAtFast (row 24 47) 24 47:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 47) 24 47 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 47) 24 47 hvalid hfast

theorem sr24p48:∀ i ∈ List.range 1,StrictCheckAt 24 (48+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 48 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 48) 24 48:=by decide +kernel
  have hfast:StrictAtFast (row 24 48) 24 48:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 48) 24 48 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 48) 24 48 hvalid hfast

theorem sr24p49:∀ i ∈ List.range 1,StrictCheckAt 24 (49+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 49 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 49) 24 49:=by decide +kernel
  have hfast:StrictAtFast (row 24 49) 24 49:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 49) 24 49 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 49) 24 49 hvalid hfast

theorem sr24p50:∀ i ∈ List.range 1,StrictCheckAt 24 (50+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 50 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 50) 24 50:=by decide +kernel
  have hfast:StrictAtFast (row 24 50) 24 50:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 50) 24 50 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 50) 24 50 hvalid hfast

theorem sr24p51:∀ i ∈ List.range 1,StrictCheckAt 24 (51+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 51 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 51) 24 51:=by decide +kernel
  have hfast:StrictAtFast (row 24 51) 24 51:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 51) 24 51 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 51) 24 51 hvalid hfast

theorem sr24p52:∀ i ∈ List.range 1,StrictCheckAt 24 (52+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 52 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 52) 24 52:=by decide +kernel
  have hfast:StrictAtFast (row 24 52) 24 52:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 52) 24 52 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 52) 24 52 hvalid hfast

theorem sr24p53:∀ i ∈ List.range 1,StrictCheckAt 24 (53+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 53 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 53) 24 53:=by decide +kernel
  have hfast:StrictAtFast (row 24 53) 24 53:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 53) 24 53 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 53) 24 53 hvalid hfast

theorem sr24p54:∀ i ∈ List.range 1,StrictCheckAt 24 (54+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 54 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 54) 24 54:=by decide +kernel
  have hfast:StrictAtFast (row 24 54) 24 54:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 54) 24 54 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 54) 24 54 hvalid hfast

theorem sr24p55:∀ i ∈ List.range 1,StrictCheckAt 24 (55+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 55 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 55) 24 55:=by decide +kernel
  have hfast:StrictAtFast (row 24 55) 24 55:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 55) 24 55 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 55) 24 55 hvalid hfast

theorem sr24p56:∀ i ∈ List.range 1,StrictCheckAt 24 (56+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 56 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 56) 24 56:=by decide +kernel
  have hfast:StrictAtFast (row 24 56) 24 56:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 56) 24 56 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 56) 24 56 hvalid hfast

theorem sr24p57:∀ i ∈ List.range 1,StrictCheckAt 24 (57+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 57 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 57) 24 57:=by decide +kernel
  have hfast:StrictAtFast (row 24 57) 24 57:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 57) 24 57 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 57) 24 57 hvalid hfast

theorem sr24p58:∀ i ∈ List.range 1,StrictCheckAt 24 (58+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 58 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 58) 24 58:=by decide +kernel
  have hfast:StrictAtFast (row 24 58) 24 58:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 58) 24 58 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 58) 24 58 hvalid hfast

theorem sr24p59:∀ i ∈ List.range 1,StrictCheckAt 24 (59+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 59 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 59) 24 59:=by decide +kernel
  have hfast:StrictAtFast (row 24 59) 24 59:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 59) 24 59 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 59) 24 59 hvalid hfast

theorem sr24p60:∀ i ∈ List.range 1,StrictCheckAt 24 (60+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 60 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 60) 24 60:=by decide +kernel
  have hfast:StrictAtFast (row 24 60) 24 60:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 60) 24 60 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 60) 24 60 hvalid hfast

theorem sr24p61:∀ i ∈ List.range 1,StrictCheckAt 24 (61+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 61 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 61) 24 61:=by decide +kernel
  have hfast:StrictAtFast (row 24 61) 24 61:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 61) 24 61 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 61) 24 61 hvalid hfast

theorem sr24p62:∀ i ∈ List.range 1,StrictCheckAt 24 (62+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 62 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 62) 24 62:=by decide +kernel
  have hfast:StrictAtFast (row 24 62) 24 62:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 62) 24 62 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 62) 24 62 hvalid hfast

theorem sr24p63:∀ i ∈ List.range 1,StrictCheckAt 24 (63+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 63 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 63) 24 63:=by decide +kernel
  have hfast:StrictAtFast (row 24 63) 24 63:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 63) 24 63 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 63) 24 63 hvalid hfast

theorem sr24p64:∀ i ∈ List.range 1,StrictCheckAt 24 (64+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 64 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 64) 24 64:=by decide +kernel
  have hfast:StrictAtFast (row 24 64) 24 64:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 64) 24 64 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 64) 24 64 hvalid hfast

theorem sr24p65:∀ i ∈ List.range 1,StrictCheckAt 24 (65+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 65 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 65) 24 65:=by decide +kernel
  have hfast:StrictAtFast (row 24 65) 24 65:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 65) 24 65 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 65) 24 65 hvalid hfast

theorem sr24p66:∀ i ∈ List.range 1,StrictCheckAt 24 (66+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 66 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 66) 24 66:=by decide +kernel
  have hfast:StrictAtFast (row 24 66) 24 66:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 66) 24 66 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 66) 24 66 hvalid hfast

theorem sr24p67:∀ i ∈ List.range 1,StrictCheckAt 24 (67+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 67 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 67) 24 67:=by decide +kernel
  have hfast:StrictAtFast (row 24 67) 24 67:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 67) 24 67 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 67) 24 67 hvalid hfast

theorem sr24p68:∀ i ∈ List.range 1,StrictCheckAt 24 (68+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 68 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 68) 24 68:=by decide +kernel
  have hfast:StrictAtFast (row 24 68) 24 68:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 68) 24 68 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 68) 24 68 hvalid hfast

theorem sr24p69:∀ i ∈ List.range 1,StrictCheckAt 24 (69+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 69 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 69) 24 69:=by decide +kernel
  have hfast:StrictAtFast (row 24 69) 24 69:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 69) 24 69 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 69) 24 69 hvalid hfast

theorem sr24p70:∀ i ∈ List.range 1,StrictCheckAt 24 (70+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 70 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 70) 24 70:=by decide +kernel
  have hfast:StrictAtFast (row 24 70) 24 70:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 70) 24 70 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 70) 24 70 hvalid hfast

theorem sr24p71:∀ i ∈ List.range 1,StrictCheckAt 24 (71+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 71 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 71) 24 71:=by decide +kernel
  have hfast:StrictAtFast (row 24 71) 24 71:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 71) 24 71 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 71) 24 71 hvalid hfast

theorem sr24p72:∀ i ∈ List.range 1,StrictCheckAt 24 (72+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 72 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 72) 24 72:=by decide +kernel
  have hfast:StrictAtFast (row 24 72) 24 72:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 72) 24 72 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 72) 24 72 hvalid hfast

theorem sr24p73:∀ i ∈ List.range 1,StrictCheckAt 24 (73+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 73 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 73) 24 73:=by decide +kernel
  have hfast:StrictAtFast (row 24 73) 24 73:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 73) 24 73 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 73) 24 73 hvalid hfast

theorem sr24p74:∀ i ∈ List.range 1,StrictCheckAt 24 (74+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 74 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 74) 24 74:=by decide +kernel
  have hfast:StrictAtFast (row 24 74) 24 74:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 74) 24 74 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 74) 24 74 hvalid hfast

theorem sr24p75:∀ i ∈ List.range 1,StrictCheckAt 24 (75+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 75 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 75) 24 75:=by decide +kernel
  have hfast:StrictAtFast (row 24 75) 24 75:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 75) 24 75 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 75) 24 75 hvalid hfast

theorem sr24p76:∀ i ∈ List.range 1,StrictCheckAt 24 (76+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 76 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 76) 24 76:=by decide +kernel
  have hfast:StrictAtFast (row 24 76) 24 76:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 76) 24 76 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 76) 24 76 hvalid hfast

theorem sr24p77:∀ i ∈ List.range 1,StrictCheckAt 24 (77+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 77 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 77) 24 77:=by decide +kernel
  have hfast:StrictAtFast (row 24 77) 24 77:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 77) 24 77 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 77) 24 77 hvalid hfast

theorem sr24p78:∀ i ∈ List.range 1,StrictCheckAt 24 (78+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 78 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 78) 24 78:=by decide +kernel
  have hfast:StrictAtFast (row 24 78) 24 78:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 78) 24 78 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 78) 24 78 hvalid hfast

theorem sr24p79:∀ i ∈ List.range 1,StrictCheckAt 24 (79+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 79 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 79) 24 79:=by decide +kernel
  have hfast:StrictAtFast (row 24 79) 24 79:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 79) 24 79 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 79) 24 79 hvalid hfast

theorem sr24p80:∀ i ∈ List.range 1,StrictCheckAt 24 (80+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 80 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 80) 24 80:=by decide +kernel
  have hfast:StrictAtFast (row 24 80) 24 80:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 80) 24 80 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 80) 24 80 hvalid hfast

theorem sr24p81:∀ i ∈ List.range 1,StrictCheckAt 24 (81+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 81 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 81) 24 81:=by decide +kernel
  have hfast:StrictAtFast (row 24 81) 24 81:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 81) 24 81 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 81) 24 81 hvalid hfast

theorem sr24p82:∀ i ∈ List.range 1,StrictCheckAt 24 (82+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 82 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 82) 24 82:=by decide +kernel
  have hfast:StrictAtFast (row 24 82) 24 82:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 82) 24 82 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 82) 24 82 hvalid hfast

theorem sr24p83:∀ i ∈ List.range 1,StrictCheckAt 24 (83+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 83 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 83) 24 83:=by decide +kernel
  have hfast:StrictAtFast (row 24 83) 24 83:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 83) 24 83 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 83) 24 83 hvalid hfast

theorem sr24p84:∀ i ∈ List.range 1,StrictCheckAt 24 (84+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 84 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 84) 24 84:=by decide +kernel
  have hfast:StrictAtFast (row 24 84) 24 84:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 84) 24 84 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 84) 24 84 hvalid hfast

theorem sr24p85:∀ i ∈ List.range 1,StrictCheckAt 24 (85+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 85 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 85) 24 85:=by decide +kernel
  have hfast:StrictAtFast (row 24 85) 24 85:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 85) 24 85 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 85) 24 85 hvalid hfast

theorem sr24p86:∀ i ∈ List.range 1,StrictCheckAt 24 (86+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 86 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 86) 24 86:=by decide +kernel
  have hfast:StrictAtFast (row 24 86) 24 86:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 86) 24 86 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 86) 24 86 hvalid hfast

theorem sr24p87:∀ i ∈ List.range 1,StrictCheckAt 24 (87+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 87 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 87) 24 87:=by decide +kernel
  have hfast:StrictAtFast (row 24 87) 24 87:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 87) 24 87 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 87) 24 87 hvalid hfast

theorem sr24p88:∀ i ∈ List.range 1,StrictCheckAt 24 (88+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 88 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 88) 24 88:=by decide +kernel
  have hfast:StrictAtFast (row 24 88) 24 88:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 88) 24 88 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 88) 24 88 hvalid hfast

theorem sr24p89:∀ i ∈ List.range 1,StrictCheckAt 24 (89+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 89 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 89) 24 89:=by decide +kernel
  have hfast:StrictAtFast (row 24 89) 24 89:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 89) 24 89 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 89) 24 89 hvalid hfast

theorem sr24p90:∀ i ∈ List.range 1,StrictCheckAt 24 (90+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 90 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 90) 24 90:=by decide +kernel
  have hfast:StrictAtFast (row 24 90) 24 90:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 90) 24 90 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 90) 24 90 hvalid hfast

theorem sr24p91:∀ i ∈ List.range 1,StrictCheckAt 24 (91+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 91 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 91) 24 91:=by decide +kernel
  have hfast:StrictAtFast (row 24 91) 24 91:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 91) 24 91 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 91) 24 91 hvalid hfast

theorem sr24p92:∀ i ∈ List.range 1,StrictCheckAt 24 (92+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 92 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 92) 24 92:=by decide +kernel
  have hfast:StrictAtFast (row 24 92) 24 92:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 92) 24 92 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 92) 24 92 hvalid hfast

theorem sr24p93:∀ i ∈ List.range 1,StrictCheckAt 24 (93+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 93 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 93) 24 93:=by decide +kernel
  have hfast:StrictAtFast (row 24 93) 24 93:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 93) 24 93 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 93) 24 93 hvalid hfast

theorem sr24p94:∀ i ∈ List.range 1,StrictCheckAt 24 (94+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 94 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 94) 24 94:=by decide +kernel
  have hfast:StrictAtFast (row 24 94) 24 94:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 94) 24 94 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 94) 24 94 hvalid hfast

theorem sr24p95:∀ i ∈ List.range 1,StrictCheckAt 24 (95+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 95 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 95) 24 95:=by decide +kernel
  have hfast:StrictAtFast (row 24 95) 24 95:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 95) 24 95 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 95) 24 95 hvalid hfast

theorem sr24p96:∀ i ∈ List.range 1,StrictCheckAt 24 (96+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 96 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 96) 24 96:=by decide +kernel
  have hfast:StrictAtFast (row 24 96) 24 96:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 96) 24 96 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 96) 24 96 hvalid hfast

theorem sr24p97:∀ i ∈ List.range 1,StrictCheckAt 24 (97+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 97 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 97) 24 97:=by decide +kernel
  have hfast:StrictAtFast (row 24 97) 24 97:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 97) 24 97 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 97) 24 97 hvalid hfast

theorem sr24p98:∀ i ∈ List.range 1,StrictCheckAt 24 (98+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 98 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 98) 24 98:=by decide +kernel
  have hfast:StrictAtFast (row 24 98) 24 98:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 98) 24 98 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 98) 24 98 hvalid hfast

theorem sr24p99:∀ i ∈ List.range 1,StrictCheckAt 24 (99+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 99 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 99) 24 99:=by decide +kernel
  have hfast:StrictAtFast (row 24 99) 24 99:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 99) 24 99 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 99) 24 99 hvalid hfast

theorem sr24p100:∀ i ∈ List.range 1,StrictCheckAt 24 (100+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 100 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 100) 24 100:=by decide +kernel
  have hfast:StrictAtFast (row 24 100) 24 100:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 100) 24 100 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 100) 24 100 hvalid hfast

theorem sr24p101:∀ i ∈ List.range 1,StrictCheckAt 24 (101+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 101 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 101) 24 101:=by decide +kernel
  have hfast:StrictAtFast (row 24 101) 24 101:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 101) 24 101 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 101) 24 101 hvalid hfast

theorem sr24p102:∀ i ∈ List.range 1,StrictCheckAt 24 (102+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 102 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 102) 24 102:=by decide +kernel
  have hfast:StrictAtFast (row 24 102) 24 102:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 102) 24 102 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 102) 24 102 hvalid hfast

theorem sr24p103:∀ i ∈ List.range 1,StrictCheckAt 24 (103+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 103 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 103) 24 103:=by decide +kernel
  have hfast:StrictAtFast (row 24 103) 24 103:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 103) 24 103 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 103) 24 103 hvalid hfast

theorem sr24p104:∀ i ∈ List.range 1,StrictCheckAt 24 (104+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 104 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 104) 24 104:=by decide +kernel
  have hfast:StrictAtFast (row 24 104) 24 104:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 104) 24 104 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 104) 24 104 hvalid hfast

theorem sr24p105:∀ i ∈ List.range 1,StrictCheckAt 24 (105+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 105 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 105) 24 105:=by decide +kernel
  have hfast:StrictAtFast (row 24 105) 24 105:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 105) 24 105 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 105) 24 105 hvalid hfast

theorem sr24p106:∀ i ∈ List.range 1,StrictCheckAt 24 (106+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 106 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 106) 24 106:=by decide +kernel
  have hfast:StrictAtFast (row 24 106) 24 106:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 106) 24 106 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 106) 24 106 hvalid hfast

theorem sr24p107:∀ i ∈ List.range 1,StrictCheckAt 24 (107+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 107 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 107) 24 107:=by decide +kernel
  have hfast:StrictAtFast (row 24 107) 24 107:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 107) 24 107 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 107) 24 107 hvalid hfast

theorem sr24p108:∀ i ∈ List.range 1,StrictCheckAt 24 (108+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 108 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 108) 24 108:=by decide +kernel
  have hfast:StrictAtFast (row 24 108) 24 108:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 108) 24 108 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 108) 24 108 hvalid hfast

theorem sr24p109:∀ i ∈ List.range 1,StrictCheckAt 24 (109+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 109 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 109) 24 109:=by decide +kernel
  have hfast:StrictAtFast (row 24 109) 24 109:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 109) 24 109 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 109) 24 109 hvalid hfast

theorem sr24p110:∀ i ∈ List.range 1,StrictCheckAt 24 (110+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 110 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 110) 24 110:=by decide +kernel
  have hfast:StrictAtFast (row 24 110) 24 110:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 110) 24 110 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 110) 24 110 hvalid hfast

theorem sr24p111:∀ i ∈ List.range 1,StrictCheckAt 24 (111+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 111 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 111) 24 111:=by decide +kernel
  have hfast:StrictAtFast (row 24 111) 24 111:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 111) 24 111 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 111) 24 111 hvalid hfast

theorem sr24p112:∀ i ∈ List.range 1,StrictCheckAt 24 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 112) 24 112:=by decide +kernel
  have hfast:StrictAtFast (row 24 112) 24 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 112) 24 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 112) 24 112 hvalid hfast

theorem sr24p113:∀ i ∈ List.range 1,StrictCheckAt 24 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 113) 24 113:=by decide +kernel
  have hfast:StrictAtFast (row 24 113) 24 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 113) 24 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 113) 24 113 hvalid hfast

theorem sr24p114:∀ i ∈ List.range 1,StrictCheckAt 24 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 114) 24 114:=by decide +kernel
  have hfast:StrictAtFast (row 24 114) 24 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 114) 24 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 114) 24 114 hvalid hfast

theorem sr24p115:∀ i ∈ List.range 1,StrictCheckAt 24 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 115) 24 115:=by decide +kernel
  have hfast:StrictAtFast (row 24 115) 24 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 115) 24 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 115) 24 115 hvalid hfast

theorem sr24p116:∀ i ∈ List.range 1,StrictCheckAt 24 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 116) 24 116:=by decide +kernel
  have hfast:StrictAtFast (row 24 116) 24 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 116) 24 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 116) 24 116 hvalid hfast

theorem sr24p117:∀ i ∈ List.range 1,StrictCheckAt 24 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 117) 24 117:=by decide +kernel
  have hfast:StrictAtFast (row 24 117) 24 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 117) 24 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 117) 24 117 hvalid hfast

theorem sr24p118:∀ i ∈ List.range 1,StrictCheckAt 24 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 24 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 24 118) 24 118:=by decide +kernel
  have hfast:StrictAtFast (row 24 118) 24 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 24 118) 24 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 24 118) 24 118 hvalid hfast

theorem br24p0:∀ i ∈ List.range 4,BaseCheckAt 24 (0+i):=by decide +kernel

theorem br24p1:∀ i ∈ List.range 4,BaseCheckAt 24 (4+i):=by decide +kernel

theorem br24p2:∀ i ∈ List.range 4,BaseCheckAt 24 (8+i):=by decide +kernel

theorem br24p3:∀ i ∈ List.range 4,BaseCheckAt 24 (12+i):=by decide +kernel

theorem br24p4:∀ i ∈ List.range 4,BaseCheckAt 24 (16+i):=by decide +kernel

theorem br24p5:∀ i ∈ List.range 4,BaseCheckAt 24 (20+i):=by decide +kernel

theorem br24p6:∀ i ∈ List.range 4,BaseCheckAt 24 (24+i):=by decide +kernel

theorem br24p7:∀ i ∈ List.range 4,BaseCheckAt 24 (28+i):=by decide +kernel

theorem br24p8:∀ i ∈ List.range 4,BaseCheckAt 24 (32+i):=by decide +kernel

theorem br24p9:∀ i ∈ List.range 4,BaseCheckAt 24 (36+i):=by decide +kernel

theorem br24p10:∀ i ∈ List.range 4,BaseCheckAt 24 (40+i):=by decide +kernel

theorem br24p11:∀ i ∈ List.range 4,BaseCheckAt 24 (44+i):=by decide +kernel

theorem br24p12:∀ i ∈ List.range 4,BaseCheckAt 24 (48+i):=by decide +kernel

theorem br24p13:∀ i ∈ List.range 4,BaseCheckAt 24 (52+i):=by decide +kernel

theorem br24p14:∀ i ∈ List.range 4,BaseCheckAt 24 (56+i):=by decide +kernel

theorem br24p15:∀ i ∈ List.range 4,BaseCheckAt 24 (60+i):=by decide +kernel



theorem br24p16:∀ i ∈ List.range 4,BaseCheckAt 24 (64+i):=by decide +kernel

theorem br24p17:∀ i ∈ List.range 4,BaseCheckAt 24 (68+i):=by decide +kernel

theorem br24p18:∀ i ∈ List.range 4,BaseCheckAt 24 (72+i):=by decide +kernel

theorem br24p19:∀ i ∈ List.range 4,BaseCheckAt 24 (76+i):=by decide +kernel

theorem br24p20:∀ i ∈ List.range 4,BaseCheckAt 24 (80+i):=by decide +kernel

theorem br24p21:∀ i ∈ List.range 4,BaseCheckAt 24 (84+i):=by decide +kernel

theorem br24p22:∀ i ∈ List.range 4,BaseCheckAt 24 (88+i):=by decide +kernel

theorem br24p23:∀ i ∈ List.range 4,BaseCheckAt 24 (92+i):=by decide +kernel

theorem br24p24:∀ i ∈ List.range 4,BaseCheckAt 24 (96+i):=by decide +kernel

theorem br24p25:∀ i ∈ List.range 4,BaseCheckAt 24 (100+i):=by decide +kernel

theorem br24p26:∀ i ∈ List.range 4,BaseCheckAt 24 (104+i):=by decide +kernel

theorem br24p27:∀ i ∈ List.range 4,BaseCheckAt 24 (108+i):=by decide +kernel

theorem br24p28:∀ i ∈ List.range 4,BaseCheckAt 24 (112+i):=by decide +kernel

theorem br24p29:∀ i ∈ List.range 3,BaseCheckAt 24 (116+i):=by decide +kernel



theorem cr24:∀ V ∈ List.range 119,CorrectAt 24 V:=by
  intro V hV
  have hv:V < 119:=List.mem_range.mp hV
  by_cases h0_15:V < 56
  · by_cases h0_7:V < 24
    · by_cases h0_3:V < 8
      · have h:=cr24p0 (V-0) (List.mem_range.mpr (by omega))
        simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
      · by_cases h1_3:V < 16
        · have h:=cr24p1 (V-8) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
        · have h:=cr24p2 (V-16) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
    · by_cases h3_7:V < 40
      · by_cases h3_5:V < 32
        · have h:=cr24p3 (V-24) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
        · have h:=cr24p4 (V-32) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
      · by_cases h5_7:V < 48
        · have h:=cr24p5 (V-40) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
        · have h:=cr24p6 (V-48) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
  · by_cases h7_15:V < 88
    · by_cases h7_11:V < 72
      · by_cases h7_9:V < 64
        · have h:=cr24p7 (V-56) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
        · have h:=cr24p8 (V-64) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
      · by_cases h9_11:V < 80
        · have h:=cr24p9 (V-72) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
        · have h:=cr24p10 (V-80) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
    · by_cases h11_15:V < 104
      · by_cases h11_13:V < 96
        · have h:=cr24p11 (V-88) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
        · have h:=cr24p12 (V-96) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
      · by_cases h13_15:V < 112
        · have h:=cr24p13 (V-104) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
        · have h:=cr24p14 (V-112) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h

theorem zr24:∀ V ∈ List.range 119,ZeroCheckAt 24 V:=by
  intro V hV
  have hv := List.mem_range.mp hV
  exact BoundaryTailZeroFromAlgebra.zeroAt_of_algebra 24 V (by omega) (by omega) (by omega)
theorem sr24:∀ V ∈ List.range 119,StrictCheckAt 24 V:=by
  intro V hV
  have hv:V < 119:=List.mem_range.mp hV
  by_cases h0_119:V < 59
  · by_cases h0_59:V < 29
    · by_cases h0_29:V < 14
      · by_cases h0_14:V < 7
        · by_cases h0_7:V < 3
          · by_cases h0_3:V < 1
            · have h:=sr24p0 (V-0) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
            · by_cases h1_3:V < 2
              · have h:=sr24p1 (V-1) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 1 ≤ V by omega)] using h
              · have h:=sr24p2 (V-2) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 2 ≤ V by omega)] using h
          · by_cases h3_7:V < 5
            · by_cases h3_5:V < 4
              · have h:=sr24p3 (V-3) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 3 ≤ V by omega)] using h
              · have h:=sr24p4 (V-4) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
            · by_cases h5_7:V < 6
              · have h:=sr24p5 (V-5) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 5 ≤ V by omega)] using h
              · have h:=sr24p6 (V-6) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 6 ≤ V by omega)] using h
        · by_cases h7_14:V < 10
          · by_cases h7_10:V < 8
            · have h:=sr24p7 (V-7) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 7 ≤ V by omega)] using h
            · by_cases h8_10:V < 9
              · have h:=sr24p8 (V-8) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
              · have h:=sr24p9 (V-9) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 9 ≤ V by omega)] using h
          · by_cases h10_14:V < 12
            · by_cases h10_12:V < 11
              · have h:=sr24p10 (V-10) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 10 ≤ V by omega)] using h
              · have h:=sr24p11 (V-11) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 11 ≤ V by omega)] using h
            · by_cases h12_14:V < 13
              · have h:=sr24p12 (V-12) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
              · have h:=sr24p13 (V-13) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 13 ≤ V by omega)] using h
      · by_cases h14_29:V < 21
        · by_cases h14_21:V < 17
          · by_cases h14_17:V < 15
            · have h:=sr24p14 (V-14) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 14 ≤ V by omega)] using h
            · by_cases h15_17:V < 16
              · have h:=sr24p15 (V-15) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 15 ≤ V by omega)] using h
              · have h:=sr24p16 (V-16) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
          · by_cases h17_21:V < 19
            · by_cases h17_19:V < 18
              · have h:=sr24p17 (V-17) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 17 ≤ V by omega)] using h
              · have h:=sr24p18 (V-18) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 18 ≤ V by omega)] using h
            · by_cases h19_21:V < 20
              · have h:=sr24p19 (V-19) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 19 ≤ V by omega)] using h
              · have h:=sr24p20 (V-20) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
        · by_cases h21_29:V < 25
          · by_cases h21_25:V < 23
            · by_cases h21_23:V < 22
              · have h:=sr24p21 (V-21) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 21 ≤ V by omega)] using h
              · have h:=sr24p22 (V-22) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 22 ≤ V by omega)] using h
            · by_cases h23_25:V < 24
              · have h:=sr24p23 (V-23) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 23 ≤ V by omega)] using h
              · have h:=sr24p24 (V-24) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
          · by_cases h25_29:V < 27
            · by_cases h25_27:V < 26
              · have h:=sr24p25 (V-25) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 25 ≤ V by omega)] using h
              · have h:=sr24p26 (V-26) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 26 ≤ V by omega)] using h
            · by_cases h27_29:V < 28
              · have h:=sr24p27 (V-27) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 27 ≤ V by omega)] using h
              · have h:=sr24p28 (V-28) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
    · by_cases h29_59:V < 44
      · by_cases h29_44:V < 36
        · by_cases h29_36:V < 32
          · by_cases h29_32:V < 30
            · have h:=sr24p29 (V-29) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 29 ≤ V by omega)] using h
            · by_cases h30_32:V < 31
              · have h:=sr24p30 (V-30) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 30 ≤ V by omega)] using h
              · have h:=sr24p31 (V-31) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 31 ≤ V by omega)] using h
          · by_cases h32_36:V < 34
            · by_cases h32_34:V < 33
              · have h:=sr24p32 (V-32) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
              · have h:=sr24p33 (V-33) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 33 ≤ V by omega)] using h
            · by_cases h34_36:V < 35
              · have h:=sr24p34 (V-34) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 34 ≤ V by omega)] using h
              · have h:=sr24p35 (V-35) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 35 ≤ V by omega)] using h
        · by_cases h36_44:V < 40
          · by_cases h36_40:V < 38
            · by_cases h36_38:V < 37
              · have h:=sr24p36 (V-36) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
              · have h:=sr24p37 (V-37) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 37 ≤ V by omega)] using h
            · by_cases h38_40:V < 39
              · have h:=sr24p38 (V-38) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 38 ≤ V by omega)] using h
              · have h:=sr24p39 (V-39) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 39 ≤ V by omega)] using h
          · by_cases h40_44:V < 42
            · by_cases h40_42:V < 41
              · have h:=sr24p40 (V-40) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
              · have h:=sr24p41 (V-41) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 41 ≤ V by omega)] using h
            · by_cases h42_44:V < 43
              · have h:=sr24p42 (V-42) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 42 ≤ V by omega)] using h
              · have h:=sr24p43 (V-43) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 43 ≤ V by omega)] using h
      · by_cases h44_59:V < 51
        · by_cases h44_51:V < 47
          · by_cases h44_47:V < 45
            · have h:=sr24p44 (V-44) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
            · by_cases h45_47:V < 46
              · have h:=sr24p45 (V-45) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 45 ≤ V by omega)] using h
              · have h:=sr24p46 (V-46) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 46 ≤ V by omega)] using h
          · by_cases h47_51:V < 49
            · by_cases h47_49:V < 48
              · have h:=sr24p47 (V-47) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 47 ≤ V by omega)] using h
              · have h:=sr24p48 (V-48) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
            · by_cases h49_51:V < 50
              · have h:=sr24p49 (V-49) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 49 ≤ V by omega)] using h
              · have h:=sr24p50 (V-50) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 50 ≤ V by omega)] using h
        · by_cases h51_59:V < 55
          · by_cases h51_55:V < 53
            · by_cases h51_53:V < 52
              · have h:=sr24p51 (V-51) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 51 ≤ V by omega)] using h
              · have h:=sr24p52 (V-52) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
            · by_cases h53_55:V < 54
              · have h:=sr24p53 (V-53) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 53 ≤ V by omega)] using h
              · have h:=sr24p54 (V-54) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 54 ≤ V by omega)] using h
          · by_cases h55_59:V < 57
            · by_cases h55_57:V < 56
              · have h:=sr24p55 (V-55) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 55 ≤ V by omega)] using h
              · have h:=sr24p56 (V-56) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
            · by_cases h57_59:V < 58
              · have h:=sr24p57 (V-57) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 57 ≤ V by omega)] using h
              · have h:=sr24p58 (V-58) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 58 ≤ V by omega)] using h
  · by_cases h59_119:V < 89
    · by_cases h59_89:V < 74
      · by_cases h59_74:V < 66
        · by_cases h59_66:V < 62
          · by_cases h59_62:V < 60
            · have h:=sr24p59 (V-59) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 59 ≤ V by omega)] using h
            · by_cases h60_62:V < 61
              · have h:=sr24p60 (V-60) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
              · have h:=sr24p61 (V-61) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 61 ≤ V by omega)] using h
          · by_cases h62_66:V < 64
            · by_cases h62_64:V < 63
              · have h:=sr24p62 (V-62) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 62 ≤ V by omega)] using h
              · have h:=sr24p63 (V-63) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 63 ≤ V by omega)] using h
            · by_cases h64_66:V < 65
              · have h:=sr24p64 (V-64) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
              · have h:=sr24p65 (V-65) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 65 ≤ V by omega)] using h
        · by_cases h66_74:V < 70
          · by_cases h66_70:V < 68
            · by_cases h66_68:V < 67
              · have h:=sr24p66 (V-66) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 66 ≤ V by omega)] using h
              · have h:=sr24p67 (V-67) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 67 ≤ V by omega)] using h
            · by_cases h68_70:V < 69
              · have h:=sr24p68 (V-68) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
              · have h:=sr24p69 (V-69) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 69 ≤ V by omega)] using h
          · by_cases h70_74:V < 72
            · by_cases h70_72:V < 71
              · have h:=sr24p70 (V-70) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 70 ≤ V by omega)] using h
              · have h:=sr24p71 (V-71) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 71 ≤ V by omega)] using h
            · by_cases h72_74:V < 73
              · have h:=sr24p72 (V-72) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
              · have h:=sr24p73 (V-73) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 73 ≤ V by omega)] using h
      · by_cases h74_89:V < 81
        · by_cases h74_81:V < 77
          · by_cases h74_77:V < 75
            · have h:=sr24p74 (V-74) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 74 ≤ V by omega)] using h
            · by_cases h75_77:V < 76
              · have h:=sr24p75 (V-75) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 75 ≤ V by omega)] using h
              · have h:=sr24p76 (V-76) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
          · by_cases h77_81:V < 79
            · by_cases h77_79:V < 78
              · have h:=sr24p77 (V-77) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 77 ≤ V by omega)] using h
              · have h:=sr24p78 (V-78) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 78 ≤ V by omega)] using h
            · by_cases h79_81:V < 80
              · have h:=sr24p79 (V-79) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 79 ≤ V by omega)] using h
              · have h:=sr24p80 (V-80) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
        · by_cases h81_89:V < 85
          · by_cases h81_85:V < 83
            · by_cases h81_83:V < 82
              · have h:=sr24p81 (V-81) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 81 ≤ V by omega)] using h
              · have h:=sr24p82 (V-82) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 82 ≤ V by omega)] using h
            · by_cases h83_85:V < 84
              · have h:=sr24p83 (V-83) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 83 ≤ V by omega)] using h
              · have h:=sr24p84 (V-84) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
          · by_cases h85_89:V < 87
            · by_cases h85_87:V < 86
              · have h:=sr24p85 (V-85) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 85 ≤ V by omega)] using h
              · have h:=sr24p86 (V-86) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 86 ≤ V by omega)] using h
            · by_cases h87_89:V < 88
              · have h:=sr24p87 (V-87) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 87 ≤ V by omega)] using h
              · have h:=sr24p88 (V-88) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
    · by_cases h89_119:V < 104
      · by_cases h89_104:V < 96
        · by_cases h89_96:V < 92
          · by_cases h89_92:V < 90
            · have h:=sr24p89 (V-89) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 89 ≤ V by omega)] using h
            · by_cases h90_92:V < 91
              · have h:=sr24p90 (V-90) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 90 ≤ V by omega)] using h
              · have h:=sr24p91 (V-91) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 91 ≤ V by omega)] using h
          · by_cases h92_96:V < 94
            · by_cases h92_94:V < 93
              · have h:=sr24p92 (V-92) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
              · have h:=sr24p93 (V-93) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 93 ≤ V by omega)] using h
            · by_cases h94_96:V < 95
              · have h:=sr24p94 (V-94) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 94 ≤ V by omega)] using h
              · have h:=sr24p95 (V-95) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 95 ≤ V by omega)] using h
        · by_cases h96_104:V < 100
          · by_cases h96_100:V < 98
            · by_cases h96_98:V < 97
              · have h:=sr24p96 (V-96) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
              · have h:=sr24p97 (V-97) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 97 ≤ V by omega)] using h
            · by_cases h98_100:V < 99
              · have h:=sr24p98 (V-98) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 98 ≤ V by omega)] using h
              · have h:=sr24p99 (V-99) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 99 ≤ V by omega)] using h
          · by_cases h100_104:V < 102
            · by_cases h100_102:V < 101
              · have h:=sr24p100 (V-100) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
              · have h:=sr24p101 (V-101) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 101 ≤ V by omega)] using h
            · by_cases h102_104:V < 103
              · have h:=sr24p102 (V-102) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 102 ≤ V by omega)] using h
              · have h:=sr24p103 (V-103) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 103 ≤ V by omega)] using h
      · by_cases h104_119:V < 111
        · by_cases h104_111:V < 107
          · by_cases h104_107:V < 105
            · have h:=sr24p104 (V-104) (List.mem_range.mpr (by omega))
              simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
            · by_cases h105_107:V < 106
              · have h:=sr24p105 (V-105) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 105 ≤ V by omega)] using h
              · have h:=sr24p106 (V-106) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 106 ≤ V by omega)] using h
          · by_cases h107_111:V < 109
            · by_cases h107_109:V < 108
              · have h:=sr24p107 (V-107) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 107 ≤ V by omega)] using h
              · have h:=sr24p108 (V-108) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
            · by_cases h109_111:V < 110
              · have h:=sr24p109 (V-109) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 109 ≤ V by omega)] using h
              · have h:=sr24p110 (V-110) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 110 ≤ V by omega)] using h
        · by_cases h111_119:V < 115
          · by_cases h111_115:V < 113
            · by_cases h111_113:V < 112
              · have h:=sr24p111 (V-111) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 111 ≤ V by omega)] using h
              · have h:=sr24p112 (V-112) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
            · by_cases h113_115:V < 114
              · have h:=sr24p113 (V-113) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 113 ≤ V by omega)] using h
              · have h:=sr24p114 (V-114) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 114 ≤ V by omega)] using h
          · by_cases h115_119:V < 117
            · by_cases h115_117:V < 116
              · have h:=sr24p115 (V-115) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 115 ≤ V by omega)] using h
              · have h:=sr24p116 (V-116) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h
            · by_cases h117_119:V < 118
              · have h:=sr24p117 (V-117) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 117 ≤ V by omega)] using h
              · have h:=sr24p118 (V-118) (List.mem_range.mpr (by omega))
                simpa only [Nat.add_sub_of_le (show 118 ≤ V by omega)] using h

theorem br24:∀ V ∈ List.range 119,BaseCheckAt 24 V:=by
  intro V hV
  have hv:V < 119:=List.mem_range.mp hV
  by_cases h0_30:V < 60
  · by_cases h0_15:V < 28
    · by_cases h0_7:V < 12
      · by_cases h0_3:V < 4
        · have h:=br24p0 (V-0) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 0 ≤ V by omega)] using h
        · by_cases h1_3:V < 8
          · have h:=br24p1 (V-4) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 4 ≤ V by omega)] using h
          · have h:=br24p2 (V-8) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 8 ≤ V by omega)] using h
      · by_cases h3_7:V < 20
        · by_cases h3_5:V < 16
          · have h:=br24p3 (V-12) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 12 ≤ V by omega)] using h
          · have h:=br24p4 (V-16) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 16 ≤ V by omega)] using h
        · by_cases h5_7:V < 24
          · have h:=br24p5 (V-20) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 20 ≤ V by omega)] using h
          · have h:=br24p6 (V-24) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 24 ≤ V by omega)] using h
    · by_cases h7_15:V < 44
      · by_cases h7_11:V < 36
        · by_cases h7_9:V < 32
          · have h:=br24p7 (V-28) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 28 ≤ V by omega)] using h
          · have h:=br24p8 (V-32) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 32 ≤ V by omega)] using h
        · by_cases h9_11:V < 40
          · have h:=br24p9 (V-36) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 36 ≤ V by omega)] using h
          · have h:=br24p10 (V-40) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 40 ≤ V by omega)] using h
      · by_cases h11_15:V < 52
        · by_cases h11_13:V < 48
          · have h:=br24p11 (V-44) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 44 ≤ V by omega)] using h
          · have h:=br24p12 (V-48) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 48 ≤ V by omega)] using h
        · by_cases h13_15:V < 56
          · have h:=br24p13 (V-52) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 52 ≤ V by omega)] using h
          · have h:=br24p14 (V-56) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 56 ≤ V by omega)] using h
  · by_cases h15_30:V < 88
    · by_cases h15_22:V < 72
      · by_cases h15_18:V < 64
        · have h:=br24p15 (V-60) (List.mem_range.mpr (by omega))
          simpa only [Nat.add_sub_of_le (show 60 ≤ V by omega)] using h
        · by_cases h16_18:V < 68
          · have h:=br24p16 (V-64) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 64 ≤ V by omega)] using h
          · have h:=br24p17 (V-68) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 68 ≤ V by omega)] using h
      · by_cases h18_22:V < 80
        · by_cases h18_20:V < 76
          · have h:=br24p18 (V-72) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 72 ≤ V by omega)] using h
          · have h:=br24p19 (V-76) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 76 ≤ V by omega)] using h
        · by_cases h20_22:V < 84
          · have h:=br24p20 (V-80) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 80 ≤ V by omega)] using h
          · have h:=br24p21 (V-84) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 84 ≤ V by omega)] using h
    · by_cases h22_30:V < 104
      · by_cases h22_26:V < 96
        · by_cases h22_24:V < 92
          · have h:=br24p22 (V-88) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 88 ≤ V by omega)] using h
          · have h:=br24p23 (V-92) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 92 ≤ V by omega)] using h
        · by_cases h24_26:V < 100
          · have h:=br24p24 (V-96) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 96 ≤ V by omega)] using h
          · have h:=br24p25 (V-100) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 100 ≤ V by omega)] using h
      · by_cases h26_30:V < 112
        · by_cases h26_28:V < 108
          · have h:=br24p26 (V-104) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 104 ≤ V by omega)] using h
          · have h:=br24p27 (V-108) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 108 ≤ V by omega)] using h
        · by_cases h28_30:V < 116
          · have h:=br24p28 (V-112) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 112 ≤ V by omega)] using h
          · have h:=br24p29 (V-116) (List.mem_range.mpr (by omega))
            simpa only [Nat.add_sub_of_le (show 116 ≤ V by omega)] using h

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
