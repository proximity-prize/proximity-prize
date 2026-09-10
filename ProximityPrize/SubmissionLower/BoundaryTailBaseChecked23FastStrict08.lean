import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r23_part112 : ∀ i ∈ List.range 1, StrictCheckAt 23 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 112) 23 112 := by decide +kernel
  exact strictAtFast_sound (row 23 112) 23 112 hvalid hfast

theorem strict_r23_part113 : ∀ i ∈ List.range 1, StrictCheckAt 23 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 113) 23 113 := by decide +kernel
  exact strictAtFast_sound (row 23 113) 23 113 hvalid hfast

theorem strict_r23_part114 : ∀ i ∈ List.range 1, StrictCheckAt 23 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 114) 23 114 := by decide +kernel
  exact strictAtFast_sound (row 23 114) 23 114 hvalid hfast

theorem strict_r23_part115 : ∀ i ∈ List.range 1, StrictCheckAt 23 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 115) 23 115 := by decide +kernel
  exact strictAtFast_sound (row 23 115) 23 115 hvalid hfast

theorem strict_r23_part116 : ∀ i ∈ List.range 1, StrictCheckAt 23 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 116) 23 116 := by decide +kernel
  exact strictAtFast_sound (row 23 116) 23 116 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
