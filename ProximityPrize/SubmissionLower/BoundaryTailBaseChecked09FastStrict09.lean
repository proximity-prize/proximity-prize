import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r9_part128 : ∀ i ∈ List.range 1, StrictCheckAt 9 (128+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 128 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 128) 9 128 := by decide +kernel
  exact strictAtFast_sound (row 9 128) 9 128 hvalid hfast

theorem strict_r9_part129 : ∀ i ∈ List.range 1, StrictCheckAt 9 (129+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 129 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 129) 9 129 := by decide +kernel
  exact strictAtFast_sound (row 9 129) 9 129 hvalid hfast

theorem strict_r9_part130 : ∀ i ∈ List.range 1, StrictCheckAt 9 (130+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 130 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 130) 9 130 := by decide +kernel
  exact strictAtFast_sound (row 9 130) 9 130 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
