import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr8p128:∀ i ∈ List.range 1,StrictCheckAt 8 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 128) 8 128:=by decide +kernel
  have hfast:StrictAtFast (row 8 128) 8 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 128) 8 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 128) 8 128 hvalid hfast

theorem sr8p129:∀ i ∈ List.range 1,StrictCheckAt 8 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 129) 8 129:=by decide +kernel
  have hfast:StrictAtFast (row 8 129) 8 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 129) 8 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 129) 8 129 hvalid hfast

theorem sr8p130:∀ i ∈ List.range 1,StrictCheckAt 8 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 130) 8 130:=by decide +kernel
  have hfast:StrictAtFast (row 8 130) 8 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 130) 8 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 130) 8 130 hvalid hfast

theorem sr8p131:∀ i ∈ List.range 1,StrictCheckAt 8 (131+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 131 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 131) 8 131:=by decide +kernel
  have hfast:StrictAtFast (row 8 131) 8 131:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 131) 8 131 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 131) 8 131 hvalid hfast

theorem sr8p132:∀ i ∈ List.range 1,StrictCheckAt 8 (132+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 132 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 132) 8 132:=by decide +kernel
  have hfast:StrictAtFast (row 8 132) 8 132:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 132) 8 132 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 132) 8 132 hvalid hfast

theorem sr8p133:∀ i ∈ List.range 1,StrictCheckAt 8 (133+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 133 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 133) 8 133:=by decide +kernel
  have hfast:StrictAtFast (row 8 133) 8 133:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 133) 8 133 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 133) 8 133 hvalid hfast

theorem sr8p134:∀ i ∈ List.range 1,StrictCheckAt 8 (134+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 8 134 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 8 134) 8 134:=by decide +kernel
  have hfast:StrictAtFast (row 8 134) 8 134:=
    BoundaryTailStrictConvex.endpoints_sound (row 8 134) 8 134 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 8 134) 8 134 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
