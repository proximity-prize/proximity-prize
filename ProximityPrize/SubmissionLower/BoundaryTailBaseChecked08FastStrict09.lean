import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r8_part128 : ∀ i ∈ List.range 1, StrictCheckAt 8 (128+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 128 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 128) 8 128 := by decide +kernel
  exact strictAtFast_sound (row 8 128) 8 128 hvalid hfast

theorem strict_r8_part129 : ∀ i ∈ List.range 1, StrictCheckAt 8 (129+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 129 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 129) 8 129 := by decide +kernel
  exact strictAtFast_sound (row 8 129) 8 129 hvalid hfast

theorem strict_r8_part130 : ∀ i ∈ List.range 1, StrictCheckAt 8 (130+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 130 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 130) 8 130 := by decide +kernel
  exact strictAtFast_sound (row 8 130) 8 130 hvalid hfast

theorem strict_r8_part131 : ∀ i ∈ List.range 1, StrictCheckAt 8 (131+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 131 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 131) 8 131 := by decide +kernel
  exact strictAtFast_sound (row 8 131) 8 131 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
