import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr27p112:∀ i ∈ List.range 1,StrictCheckAt 27 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 112 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 112) 27 112:=by decide +kernel
  exact strictAtFast_sound (row 27 112) 27 112 hvalid hfast

theorem sr27p113:∀ i ∈ List.range 1,StrictCheckAt 27 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 113 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 113) 27 113:=by decide +kernel
  exact strictAtFast_sound (row 27 113) 27 113 hvalid hfast

theorem sr27p114:∀ i ∈ List.range 1,StrictCheckAt 27 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 114 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 114) 27 114:=by decide +kernel
  exact strictAtFast_sound (row 27 114) 27 114 hvalid hfast

theorem sr27p115:∀ i ∈ List.range 1,StrictCheckAt 27 (115+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 27 115 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 27 115) 27 115:=by decide +kernel
  exact strictAtFast_sound (row 27 115) 27 115 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
