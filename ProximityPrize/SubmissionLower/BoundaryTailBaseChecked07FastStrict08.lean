import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr7p112:∀ i ∈ List.range 1,StrictCheckAt 7 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 112) 7 112:=by decide +kernel
  have hfast:StrictAtFast (row 7 112) 7 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 112) 7 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 112) 7 112 hvalid hfast

theorem sr7p113:∀ i ∈ List.range 1,StrictCheckAt 7 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 113) 7 113:=by decide +kernel
  have hfast:StrictAtFast (row 7 113) 7 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 113) 7 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 113) 7 113 hvalid hfast

theorem sr7p114:∀ i ∈ List.range 1,StrictCheckAt 7 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 114) 7 114:=by decide +kernel
  have hfast:StrictAtFast (row 7 114) 7 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 114) 7 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 114) 7 114 hvalid hfast

theorem sr7p115:∀ i ∈ List.range 1,StrictCheckAt 7 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 115) 7 115:=by decide +kernel
  have hfast:StrictAtFast (row 7 115) 7 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 115) 7 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 115) 7 115 hvalid hfast

theorem sr7p116:∀ i ∈ List.range 1,StrictCheckAt 7 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 116) 7 116:=by decide +kernel
  have hfast:StrictAtFast (row 7 116) 7 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 116) 7 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 116) 7 116 hvalid hfast

theorem sr7p117:∀ i ∈ List.range 1,StrictCheckAt 7 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 117) 7 117:=by decide +kernel
  have hfast:StrictAtFast (row 7 117) 7 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 117) 7 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 117) 7 117 hvalid hfast

theorem sr7p118:∀ i ∈ List.range 1,StrictCheckAt 7 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 118) 7 118:=by decide +kernel
  have hfast:StrictAtFast (row 7 118) 7 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 118) 7 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 118) 7 118 hvalid hfast

theorem sr7p119:∀ i ∈ List.range 1,StrictCheckAt 7 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 119) 7 119:=by decide +kernel
  have hfast:StrictAtFast (row 7 119) 7 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 119) 7 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 119) 7 119 hvalid hfast

theorem sr7p120:∀ i ∈ List.range 1,StrictCheckAt 7 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 120) 7 120:=by decide +kernel
  have hfast:StrictAtFast (row 7 120) 7 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 120) 7 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 120) 7 120 hvalid hfast

theorem sr7p121:∀ i ∈ List.range 1,StrictCheckAt 7 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 121) 7 121:=by decide +kernel
  have hfast:StrictAtFast (row 7 121) 7 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 121) 7 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 121) 7 121 hvalid hfast

theorem sr7p122:∀ i ∈ List.range 1,StrictCheckAt 7 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 122) 7 122:=by decide +kernel
  have hfast:StrictAtFast (row 7 122) 7 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 122) 7 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 122) 7 122 hvalid hfast

theorem sr7p123:∀ i ∈ List.range 1,StrictCheckAt 7 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 123) 7 123:=by decide +kernel
  have hfast:StrictAtFast (row 7 123) 7 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 123) 7 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 123) 7 123 hvalid hfast

theorem sr7p124:∀ i ∈ List.range 1,StrictCheckAt 7 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 124) 7 124:=by decide +kernel
  have hfast:StrictAtFast (row 7 124) 7 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 124) 7 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 124) 7 124 hvalid hfast

theorem sr7p125:∀ i ∈ List.range 1,StrictCheckAt 7 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 125) 7 125:=by decide +kernel
  have hfast:StrictAtFast (row 7 125) 7 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 125) 7 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 125) 7 125 hvalid hfast

theorem sr7p126:∀ i ∈ List.range 1,StrictCheckAt 7 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 126) 7 126:=by decide +kernel
  have hfast:StrictAtFast (row 7 126) 7 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 126) 7 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 126) 7 126 hvalid hfast

theorem sr7p127:∀ i ∈ List.range 1,StrictCheckAt 7 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 7 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 7 127) 7 127:=by decide +kernel
  have hfast:StrictAtFast (row 7 127) 7 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 7 127) 7 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 7 127) 7 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
