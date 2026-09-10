import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r24_part112 : ∀ i ∈ List.range 1, StrictCheckAt 24 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 112) 24 112 := by decide +kernel
  exact strictAtFast_sound (row 24 112) 24 112 hvalid hfast

theorem strict_r24_part113 : ∀ i ∈ List.range 1, StrictCheckAt 24 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 113) 24 113 := by decide +kernel
  exact strictAtFast_sound (row 24 113) 24 113 hvalid hfast

theorem strict_r24_part114 : ∀ i ∈ List.range 1, StrictCheckAt 24 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 114) 24 114 := by decide +kernel
  exact strictAtFast_sound (row 24 114) 24 114 hvalid hfast

theorem strict_r24_part115 : ∀ i ∈ List.range 1, StrictCheckAt 24 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 115) 24 115 := by decide +kernel
  exact strictAtFast_sound (row 24 115) 24 115 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
