import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r19_part112 : ∀ i ∈ List.range 1, StrictCheckAt 19 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 112) 19 112 := by decide +kernel
  exact strictAtFast_sound (row 19 112) 19 112 hvalid hfast

theorem strict_r19_part113 : ∀ i ∈ List.range 1, StrictCheckAt 19 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 113) 19 113 := by decide +kernel
  exact strictAtFast_sound (row 19 113) 19 113 hvalid hfast

theorem strict_r19_part114 : ∀ i ∈ List.range 1, StrictCheckAt 19 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 114) 19 114 := by decide +kernel
  exact strictAtFast_sound (row 19 114) 19 114 hvalid hfast

theorem strict_r19_part115 : ∀ i ∈ List.range 1, StrictCheckAt 19 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 115) 19 115 := by decide +kernel
  exact strictAtFast_sound (row 19 115) 19 115 hvalid hfast

theorem strict_r19_part116 : ∀ i ∈ List.range 1, StrictCheckAt 19 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 116) 19 116 := by decide +kernel
  exact strictAtFast_sound (row 19 116) 19 116 hvalid hfast

theorem strict_r19_part117 : ∀ i ∈ List.range 1, StrictCheckAt 19 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 117) 19 117 := by decide +kernel
  exact strictAtFast_sound (row 19 117) 19 117 hvalid hfast

theorem strict_r19_part118 : ∀ i ∈ List.range 1, StrictCheckAt 19 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 118) 19 118 := by decide +kernel
  exact strictAtFast_sound (row 19 118) 19 118 hvalid hfast

theorem strict_r19_part119 : ∀ i ∈ List.range 1, StrictCheckAt 19 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 119) 19 119 := by decide +kernel
  exact strictAtFast_sound (row 19 119) 19 119 hvalid hfast

theorem strict_r19_part120 : ∀ i ∈ List.range 1, StrictCheckAt 19 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 120) 19 120 := by decide +kernel
  exact strictAtFast_sound (row 19 120) 19 120 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
