import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r25_part112 : ∀ i ∈ List.range 1, StrictCheckAt 25 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 112) 25 112 := by decide +kernel
  exact strictAtFast_sound (row 25 112) 25 112 hvalid hfast

theorem strict_r25_part113 : ∀ i ∈ List.range 1, StrictCheckAt 25 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 113) 25 113 := by decide +kernel
  exact strictAtFast_sound (row 25 113) 25 113 hvalid hfast

theorem strict_r25_part114 : ∀ i ∈ List.range 1, StrictCheckAt 25 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 114) 25 114 := by decide +kernel
  exact strictAtFast_sound (row 25 114) 25 114 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
