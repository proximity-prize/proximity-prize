import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr13p112:∀ i ∈ List.range 1,StrictCheckAt 13 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 112) 13 112:=by decide +kernel
  have hfast:StrictAtFast (row 13 112) 13 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 112) 13 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 112) 13 112 hvalid hfast

theorem sr13p113:∀ i ∈ List.range 1,StrictCheckAt 13 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 113) 13 113:=by decide +kernel
  have hfast:StrictAtFast (row 13 113) 13 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 113) 13 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 113) 13 113 hvalid hfast

theorem sr13p114:∀ i ∈ List.range 1,StrictCheckAt 13 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 114) 13 114:=by decide +kernel
  have hfast:StrictAtFast (row 13 114) 13 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 114) 13 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 114) 13 114 hvalid hfast

theorem sr13p115:∀ i ∈ List.range 1,StrictCheckAt 13 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 115) 13 115:=by decide +kernel
  have hfast:StrictAtFast (row 13 115) 13 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 115) 13 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 115) 13 115 hvalid hfast

theorem sr13p116:∀ i ∈ List.range 1,StrictCheckAt 13 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 116) 13 116:=by decide +kernel
  have hfast:StrictAtFast (row 13 116) 13 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 116) 13 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 116) 13 116 hvalid hfast

theorem sr13p117:∀ i ∈ List.range 1,StrictCheckAt 13 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 117) 13 117:=by decide +kernel
  have hfast:StrictAtFast (row 13 117) 13 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 117) 13 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 117) 13 117 hvalid hfast

theorem sr13p118:∀ i ∈ List.range 1,StrictCheckAt 13 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 118) 13 118:=by decide +kernel
  have hfast:StrictAtFast (row 13 118) 13 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 118) 13 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 118) 13 118 hvalid hfast

theorem sr13p119:∀ i ∈ List.range 1,StrictCheckAt 13 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 119) 13 119:=by decide +kernel
  have hfast:StrictAtFast (row 13 119) 13 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 119) 13 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 119) 13 119 hvalid hfast

theorem sr13p120:∀ i ∈ List.range 1,StrictCheckAt 13 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 120) 13 120:=by decide +kernel
  have hfast:StrictAtFast (row 13 120) 13 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 120) 13 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 120) 13 120 hvalid hfast

theorem sr13p121:∀ i ∈ List.range 1,StrictCheckAt 13 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 121) 13 121:=by decide +kernel
  have hfast:StrictAtFast (row 13 121) 13 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 121) 13 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 121) 13 121 hvalid hfast

theorem sr13p122:∀ i ∈ List.range 1,StrictCheckAt 13 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 122) 13 122:=by decide +kernel
  have hfast:StrictAtFast (row 13 122) 13 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 122) 13 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 122) 13 122 hvalid hfast

theorem sr13p123:∀ i ∈ List.range 1,StrictCheckAt 13 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 123) 13 123:=by decide +kernel
  have hfast:StrictAtFast (row 13 123) 13 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 123) 13 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 123) 13 123 hvalid hfast

theorem sr13p124:∀ i ∈ List.range 1,StrictCheckAt 13 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 124) 13 124:=by decide +kernel
  have hfast:StrictAtFast (row 13 124) 13 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 124) 13 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 124) 13 124 hvalid hfast

theorem sr13p125:∀ i ∈ List.range 1,StrictCheckAt 13 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 125) 13 125:=by decide +kernel
  have hfast:StrictAtFast (row 13 125) 13 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 125) 13 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 125) 13 125 hvalid hfast

theorem sr13p126:∀ i ∈ List.range 1,StrictCheckAt 13 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 126) 13 126:=by decide +kernel
  have hfast:StrictAtFast (row 13 126) 13 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 126) 13 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 126) 13 126 hvalid hfast

theorem sr13p127:∀ i ∈ List.range 1,StrictCheckAt 13 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 13 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 13 127) 13 127:=by decide +kernel
  have hfast:StrictAtFast (row 13 127) 13 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 13 127) 13 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 13 127) 13 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
