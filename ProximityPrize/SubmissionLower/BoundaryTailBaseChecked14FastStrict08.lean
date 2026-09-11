import ProximityPrize.SubmissionLower.BoundaryTailStrictCurvature
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p112:∀ i ∈ List.range 1,StrictCheckAt 14 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 112 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 112) 14 112:=by decide +kernel
  have hfast:StrictAtFast (row 14 112) 14 112:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 112) 14 112 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 112) 14 112 hvalid hfast

theorem sr14p113:∀ i ∈ List.range 1,StrictCheckAt 14 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 113 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 113) 14 113:=by decide +kernel
  have hfast:StrictAtFast (row 14 113) 14 113:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 113) 14 113 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 113) 14 113 hvalid hfast

theorem sr14p114:∀ i ∈ List.range 1,StrictCheckAt 14 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 114 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 114) 14 114:=by decide +kernel
  have hfast:StrictAtFast (row 14 114) 14 114:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 114) 14 114 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 114) 14 114 hvalid hfast

theorem sr14p115:∀ i ∈ List.range 1,StrictCheckAt 14 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 115 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 115) 14 115:=by decide +kernel
  have hfast:StrictAtFast (row 14 115) 14 115:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 115) 14 115 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 115) 14 115 hvalid hfast

theorem sr14p116:∀ i ∈ List.range 1,StrictCheckAt 14 (116+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 116 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 116) 14 116:=by decide +kernel
  have hfast:StrictAtFast (row 14 116) 14 116:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 116) 14 116 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 116) 14 116 hvalid hfast

theorem sr14p117:∀ i ∈ List.range 1,StrictCheckAt 14 (117+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 117 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 117) 14 117:=by decide +kernel
  have hfast:StrictAtFast (row 14 117) 14 117:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 117) 14 117 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 117) 14 117 hvalid hfast

theorem sr14p118:∀ i ∈ List.range 1,StrictCheckAt 14 (118+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 118 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 118) 14 118:=by decide +kernel
  have hfast:StrictAtFast (row 14 118) 14 118:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 118) 14 118 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 118) 14 118 hvalid hfast

theorem sr14p119:∀ i ∈ List.range 1,StrictCheckAt 14 (119+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 119 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 119) 14 119:=by decide +kernel
  have hfast:StrictAtFast (row 14 119) 14 119:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 119) 14 119 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 119) 14 119 hvalid hfast

theorem sr14p120:∀ i ∈ List.range 1,StrictCheckAt 14 (120+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 120 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 120) 14 120:=by decide +kernel
  have hfast:StrictAtFast (row 14 120) 14 120:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 120) 14 120 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 120) 14 120 hvalid hfast

theorem sr14p121:∀ i ∈ List.range 1,StrictCheckAt 14 (121+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 121 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 121) 14 121:=by decide +kernel
  have hfast:StrictAtFast (row 14 121) 14 121:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 121) 14 121 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 121) 14 121 hvalid hfast

theorem sr14p122:∀ i ∈ List.range 1,StrictCheckAt 14 (122+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 122 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 122) 14 122:=by decide +kernel
  have hfast:StrictAtFast (row 14 122) 14 122:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 122) 14 122 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 122) 14 122 hvalid hfast

theorem sr14p123:∀ i ∈ List.range 1,StrictCheckAt 14 (123+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 123 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 123) 14 123:=by decide +kernel
  have hfast:StrictAtFast (row 14 123) 14 123:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 123) 14 123 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 123) 14 123 hvalid hfast

theorem sr14p124:∀ i ∈ List.range 1,StrictCheckAt 14 (124+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 124 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 124) 14 124:=by decide +kernel
  have hfast:StrictAtFast (row 14 124) 14 124:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 124) 14 124 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 124) 14 124 hvalid hfast

theorem sr14p125:∀ i ∈ List.range 1,StrictCheckAt 14 (125+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 125 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 125) 14 125:=by decide +kernel
  have hfast:StrictAtFast (row 14 125) 14 125:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 125) 14 125 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 125) 14 125 hvalid hfast

theorem sr14p126:∀ i ∈ List.range 1,StrictCheckAt 14 (126+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 126 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 126) 14 126:=by decide +kernel
  have hfast:StrictAtFast (row 14 126) 14 126:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 126) 14 126 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 126) 14 126 hvalid hfast

theorem sr14p127:∀ i ∈ List.range 1,StrictCheckAt 14 (127+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 127 (by omega) (by omega) (by omega)
  have hend:BoundaryTailStrictConvex.Endpoints (row 14 127) 14 127:=by decide +kernel
  have hfast:StrictAtFast (row 14 127) 14 127:=
    BoundaryTailStrictConvex.endpoints_sound (row 14 127) 14 127 (by omega)
      BoundaryTailStrictConvex.curvatureAll (by omega) hend
  exact strictAtFast_sound (row 14 127) 14 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
