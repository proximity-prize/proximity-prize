import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr22p112:∀ i ∈ List.range 1,StrictCheckAt 22 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 112) 22 112:=by decide +kernel
  have hfast:StrictAtFast (row 22 112) 22 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 112) 22 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 112) 22 112 hvalid hfast

theorem sr22p113:∀ i ∈ List.range 1,StrictCheckAt 22 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 113) 22 113:=by decide +kernel
  have hfast:StrictAtFast (row 22 113) 22 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 113) 22 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 113) 22 113 hvalid hfast

theorem sr22p114:∀ i ∈ List.range 1,StrictCheckAt 22 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 114) 22 114:=by decide +kernel
  have hfast:StrictAtFast (row 22 114) 22 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 114) 22 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 114) 22 114 hvalid hfast

theorem sr22p115:∀ i ∈ List.range 1,StrictCheckAt 22 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 115) 22 115:=by decide +kernel
  have hfast:StrictAtFast (row 22 115) 22 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 115) 22 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 115) 22 115 hvalid hfast

theorem sr22p116:∀ i ∈ List.range 1,StrictCheckAt 22 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 116) 22 116:=by decide +kernel
  have hfast:StrictAtFast (row 22 116) 22 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 116) 22 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 116) 22 116 hvalid hfast

theorem sr22p117:∀ i ∈ List.range 1,StrictCheckAt 22 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 117) 22 117:=by decide +kernel
  have hfast:StrictAtFast (row 22 117) 22 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 117) 22 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 117) 22 117 hvalid hfast

theorem sr22p118:∀ i ∈ List.range 1,StrictCheckAt 22 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 118) 22 118:=by decide +kernel
  have hfast:StrictAtFast (row 22 118) 22 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 118) 22 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 118) 22 118 hvalid hfast

theorem sr22p119:∀ i ∈ List.range 1,StrictCheckAt 22 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 119) 22 119:=by decide +kernel
  have hfast:StrictAtFast (row 22 119) 22 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 119) 22 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 119) 22 119 hvalid hfast

theorem sr22p120:∀ i ∈ List.range 1,StrictCheckAt 22 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 22 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 22 120) 22 120:=by decide +kernel
  have hfast:StrictAtFast (row 22 120) 22 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 22 120) 22 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 22 120) 22 120 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
