import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r20_part112 : ∀ i ∈ List.range 1, StrictCheckAt 20 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 112) 20 112 := by decide +kernel
  exact strictAtFast_sound (row 20 112) 20 112 hvalid hfast

theorem strict_r20_part113 : ∀ i ∈ List.range 1, StrictCheckAt 20 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 113) 20 113 := by decide +kernel
  exact strictAtFast_sound (row 20 113) 20 113 hvalid hfast

theorem strict_r20_part114 : ∀ i ∈ List.range 1, StrictCheckAt 20 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 114) 20 114 := by decide +kernel
  exact strictAtFast_sound (row 20 114) 20 114 hvalid hfast

theorem strict_r20_part115 : ∀ i ∈ List.range 1, StrictCheckAt 20 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 115) 20 115 := by decide +kernel
  exact strictAtFast_sound (row 20 115) 20 115 hvalid hfast

theorem strict_r20_part116 : ∀ i ∈ List.range 1, StrictCheckAt 20 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 116) 20 116 := by decide +kernel
  exact strictAtFast_sound (row 20 116) 20 116 hvalid hfast

theorem strict_r20_part117 : ∀ i ∈ List.range 1, StrictCheckAt 20 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 117) 20 117 := by decide +kernel
  exact strictAtFast_sound (row 20 117) 20 117 hvalid hfast

theorem strict_r20_part118 : ∀ i ∈ List.range 1, StrictCheckAt 20 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 118) 20 118 := by decide +kernel
  exact strictAtFast_sound (row 20 118) 20 118 hvalid hfast

theorem strict_r20_part119 : ∀ i ∈ List.range 1, StrictCheckAt 20 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 119) 20 119 := by decide +kernel
  exact strictAtFast_sound (row 20 119) 20 119 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
