import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr29p112:∀ i ∈ List.range 1,StrictCheckAt 29 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 112 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 112) 29 112:=by decide +kernel
  exact strictAtFast_sound (row 29 112) 29 112 hvalid hfast

theorem sr29p113:∀ i ∈ List.range 1,StrictCheckAt 29 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 29 113 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 29 113) 29 113:=by decide +kernel
  exact strictAtFast_sound (row 29 113) 29 113 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
