import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr14p128:∀ i ∈ List.range 1,StrictCheckAt 14 (128+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 14 128 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 14 128) 14 128:=by decide +kernel
  exact strictAtFast_sound (row 14 128) 14 128 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
