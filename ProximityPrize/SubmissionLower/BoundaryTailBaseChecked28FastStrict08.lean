import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem sr28p112:∀ i ∈ List.range 1,StrictCheckAt 28 (112+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 112 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 112) 28 112:=by decide +kernel
  exact strictAtFast_sound (row 28 112) 28 112 hvalid hfast

theorem sr28p113:∀ i ∈ List.range 1,StrictCheckAt 28 (113+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 113 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 113) 28 113:=by decide +kernel
  exact strictAtFast_sound (row 28 113) 28 113 hvalid hfast

theorem sr28p114:∀ i ∈ List.range 1,StrictCheckAt 28 (114+i):=by
  intro i hi
  have hi0:i = 0:=by have:=List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid:=validAll 28 114 (by omega) (by omega) (by omega)
  have hfast:StrictAtFast (row 28 114) 28 114:=by decide +kernel
  exact strictAtFast_sound (row 28 114) 28 114 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
