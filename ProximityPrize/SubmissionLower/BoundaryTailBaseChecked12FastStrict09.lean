import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr12p128:∀ i ∈ List.range 1,StrictCheckAt 12 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 128 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 128) 12 128:=by decide +kernel
  have hfast:StrictAtFast (row 12 128) 12 128:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 128) 12 128 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 128) 12 128 hvalid hfast

theorem sr12p129:∀ i ∈ List.range 1,StrictCheckAt 12 (129+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 129 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 129) 12 129:=by decide +kernel
  have hfast:StrictAtFast (row 12 129) 12 129:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 129) 12 129 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 129) 12 129 hvalid hfast

theorem sr12p130:∀ i ∈ List.range 1,StrictCheckAt 12 (130+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 12 130 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 12 130) 12 130:=by decide +kernel
  have hfast:StrictAtFast (row 12 130) 12 130:=
    BoundaryTailStrictConvex.endpoints_sound (row 12 130) 12 130 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 12 130) 12 130 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
