import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr16p112:∀ i ∈ List.range 1,StrictCheckAt 16 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 112) 16 112:=by decide +kernel
  have hfast:StrictAtFast (row 16 112) 16 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 112) 16 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 112) 16 112 hvalid hfast

theorem sr16p113:∀ i ∈ List.range 1,StrictCheckAt 16 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 113) 16 113:=by decide +kernel
  have hfast:StrictAtFast (row 16 113) 16 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 113) 16 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 113) 16 113 hvalid hfast

theorem sr16p114:∀ i ∈ List.range 1,StrictCheckAt 16 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 114) 16 114:=by decide +kernel
  have hfast:StrictAtFast (row 16 114) 16 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 114) 16 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 114) 16 114 hvalid hfast

theorem sr16p115:∀ i ∈ List.range 1,StrictCheckAt 16 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 115) 16 115:=by decide +kernel
  have hfast:StrictAtFast (row 16 115) 16 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 115) 16 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 115) 16 115 hvalid hfast

theorem sr16p116:∀ i ∈ List.range 1,StrictCheckAt 16 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 116) 16 116:=by decide +kernel
  have hfast:StrictAtFast (row 16 116) 16 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 116) 16 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 116) 16 116 hvalid hfast

theorem sr16p117:∀ i ∈ List.range 1,StrictCheckAt 16 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 117) 16 117:=by decide +kernel
  have hfast:StrictAtFast (row 16 117) 16 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 117) 16 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 117) 16 117 hvalid hfast

theorem sr16p118:∀ i ∈ List.range 1,StrictCheckAt 16 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 118) 16 118:=by decide +kernel
  have hfast:StrictAtFast (row 16 118) 16 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 118) 16 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 118) 16 118 hvalid hfast

theorem sr16p119:∀ i ∈ List.range 1,StrictCheckAt 16 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 119) 16 119:=by decide +kernel
  have hfast:StrictAtFast (row 16 119) 16 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 119) 16 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 119) 16 119 hvalid hfast

theorem sr16p120:∀ i ∈ List.range 1,StrictCheckAt 16 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 120) 16 120:=by decide +kernel
  have hfast:StrictAtFast (row 16 120) 16 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 120) 16 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 120) 16 120 hvalid hfast

theorem sr16p121:∀ i ∈ List.range 1,StrictCheckAt 16 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 121) 16 121:=by decide +kernel
  have hfast:StrictAtFast (row 16 121) 16 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 121) 16 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 121) 16 121 hvalid hfast

theorem sr16p122:∀ i ∈ List.range 1,StrictCheckAt 16 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 122) 16 122:=by decide +kernel
  have hfast:StrictAtFast (row 16 122) 16 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 122) 16 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 122) 16 122 hvalid hfast

theorem sr16p123:∀ i ∈ List.range 1,StrictCheckAt 16 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 123) 16 123:=by decide +kernel
  have hfast:StrictAtFast (row 16 123) 16 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 123) 16 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 123) 16 123 hvalid hfast

theorem sr16p124:∀ i ∈ List.range 1,StrictCheckAt 16 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 124) 16 124:=by decide +kernel
  have hfast:StrictAtFast (row 16 124) 16 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 124) 16 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 124) 16 124 hvalid hfast

theorem sr16p125:∀ i ∈ List.range 1,StrictCheckAt 16 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 125) 16 125:=by decide +kernel
  have hfast:StrictAtFast (row 16 125) 16 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 125) 16 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 125) 16 125 hvalid hfast

theorem sr16p126:∀ i ∈ List.range 1,StrictCheckAt 16 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 16 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 16 126) 16 126:=by decide +kernel
  have hfast:StrictAtFast (row 16 126) 16 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 16 126) 16 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 16 126) 16 126 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
