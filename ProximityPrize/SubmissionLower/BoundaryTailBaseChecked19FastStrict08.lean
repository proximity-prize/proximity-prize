import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr19p112:∀ i ∈ List.range 1,StrictCheckAt 19 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 112) 19 112:=by decide +kernel
  have hfast:StrictAtFast (row 19 112) 19 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 112) 19 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 112) 19 112 hvalid hfast

theorem sr19p113:∀ i ∈ List.range 1,StrictCheckAt 19 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 113) 19 113:=by decide +kernel
  have hfast:StrictAtFast (row 19 113) 19 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 113) 19 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 113) 19 113 hvalid hfast

theorem sr19p114:∀ i ∈ List.range 1,StrictCheckAt 19 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 114) 19 114:=by decide +kernel
  have hfast:StrictAtFast (row 19 114) 19 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 114) 19 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 114) 19 114 hvalid hfast

theorem sr19p115:∀ i ∈ List.range 1,StrictCheckAt 19 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 115) 19 115:=by decide +kernel
  have hfast:StrictAtFast (row 19 115) 19 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 115) 19 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 115) 19 115 hvalid hfast

theorem sr19p116:∀ i ∈ List.range 1,StrictCheckAt 19 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 116) 19 116:=by decide +kernel
  have hfast:StrictAtFast (row 19 116) 19 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 116) 19 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 116) 19 116 hvalid hfast

theorem sr19p117:∀ i ∈ List.range 1,StrictCheckAt 19 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 117) 19 117:=by decide +kernel
  have hfast:StrictAtFast (row 19 117) 19 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 117) 19 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 117) 19 117 hvalid hfast

theorem sr19p118:∀ i ∈ List.range 1,StrictCheckAt 19 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 118) 19 118:=by decide +kernel
  have hfast:StrictAtFast (row 19 118) 19 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 118) 19 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 118) 19 118 hvalid hfast

theorem sr19p119:∀ i ∈ List.range 1,StrictCheckAt 19 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 119) 19 119:=by decide +kernel
  have hfast:StrictAtFast (row 19 119) 19 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 119) 19 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 119) 19 119 hvalid hfast

theorem sr19p120:∀ i ∈ List.range 1,StrictCheckAt 19 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 120) 19 120:=by decide +kernel
  have hfast:StrictAtFast (row 19 120) 19 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 120) 19 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 120) 19 120 hvalid hfast

theorem sr19p121:∀ i ∈ List.range 1,StrictCheckAt 19 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 121) 19 121:=by decide +kernel
  have hfast:StrictAtFast (row 19 121) 19 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 121) 19 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 121) 19 121 hvalid hfast

theorem sr19p122:∀ i ∈ List.range 1,StrictCheckAt 19 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 122) 19 122:=by decide +kernel
  have hfast:StrictAtFast (row 19 122) 19 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 122) 19 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 122) 19 122 hvalid hfast

theorem sr19p123:∀ i ∈ List.range 1,StrictCheckAt 19 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 19 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 19 123) 19 123:=by decide +kernel
  have hfast:StrictAtFast (row 19 123) 19 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 19 123) 19 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 19 123) 19 123 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
