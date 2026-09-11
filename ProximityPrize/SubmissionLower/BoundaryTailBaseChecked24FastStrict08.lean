import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

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

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
