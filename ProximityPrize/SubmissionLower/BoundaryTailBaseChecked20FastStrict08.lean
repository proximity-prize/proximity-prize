import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr20p112:∀ i ∈ List.range 1,StrictCheckAt 20 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 112) 20 112:=by decide +kernel
  have hfast:StrictAtFast (row 20 112) 20 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 112) 20 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 112) 20 112 hvalid hfast

theorem sr20p113:∀ i ∈ List.range 1,StrictCheckAt 20 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 113) 20 113:=by decide +kernel
  have hfast:StrictAtFast (row 20 113) 20 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 113) 20 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 113) 20 113 hvalid hfast

theorem sr20p114:∀ i ∈ List.range 1,StrictCheckAt 20 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 114) 20 114:=by decide +kernel
  have hfast:StrictAtFast (row 20 114) 20 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 114) 20 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 114) 20 114 hvalid hfast

theorem sr20p115:∀ i ∈ List.range 1,StrictCheckAt 20 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 115) 20 115:=by decide +kernel
  have hfast:StrictAtFast (row 20 115) 20 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 115) 20 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 115) 20 115 hvalid hfast

theorem sr20p116:∀ i ∈ List.range 1,StrictCheckAt 20 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 116) 20 116:=by decide +kernel
  have hfast:StrictAtFast (row 20 116) 20 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 116) 20 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 116) 20 116 hvalid hfast

theorem sr20p117:∀ i ∈ List.range 1,StrictCheckAt 20 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 117) 20 117:=by decide +kernel
  have hfast:StrictAtFast (row 20 117) 20 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 117) 20 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 117) 20 117 hvalid hfast

theorem sr20p118:∀ i ∈ List.range 1,StrictCheckAt 20 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 118) 20 118:=by decide +kernel
  have hfast:StrictAtFast (row 20 118) 20 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 118) 20 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 118) 20 118 hvalid hfast

theorem sr20p119:∀ i ∈ List.range 1,StrictCheckAt 20 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 119) 20 119:=by decide +kernel
  have hfast:StrictAtFast (row 20 119) 20 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 119) 20 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 119) 20 119 hvalid hfast

theorem sr20p120:∀ i ∈ List.range 1,StrictCheckAt 20 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 120) 20 120:=by decide +kernel
  have hfast:StrictAtFast (row 20 120) 20 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 120) 20 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 120) 20 120 hvalid hfast

theorem sr20p121:∀ i ∈ List.range 1,StrictCheckAt 20 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 121) 20 121:=by decide +kernel
  have hfast:StrictAtFast (row 20 121) 20 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 121) 20 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 121) 20 121 hvalid hfast

theorem sr20p122:∀ i ∈ List.range 1,StrictCheckAt 20 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 20 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 20 122) 20 122:=by decide +kernel
  have hfast:StrictAtFast (row 20 122) 20 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 20 122) 20 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 20 122) 20 122 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
