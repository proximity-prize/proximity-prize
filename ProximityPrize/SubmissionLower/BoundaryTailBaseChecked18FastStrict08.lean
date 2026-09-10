import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r18_part112 : ∀ i ∈ List.range 1, StrictCheckAt 18 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 112) 18 112 := by decide +kernel
  exact strictAtFast_sound (row 18 112) 18 112 hvalid hfast

theorem strict_r18_part113 : ∀ i ∈ List.range 1, StrictCheckAt 18 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 113) 18 113 := by decide +kernel
  exact strictAtFast_sound (row 18 113) 18 113 hvalid hfast

theorem strict_r18_part114 : ∀ i ∈ List.range 1, StrictCheckAt 18 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 114) 18 114 := by decide +kernel
  exact strictAtFast_sound (row 18 114) 18 114 hvalid hfast

theorem strict_r18_part115 : ∀ i ∈ List.range 1, StrictCheckAt 18 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 115) 18 115 := by decide +kernel
  exact strictAtFast_sound (row 18 115) 18 115 hvalid hfast

theorem strict_r18_part116 : ∀ i ∈ List.range 1, StrictCheckAt 18 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 116) 18 116 := by decide +kernel
  exact strictAtFast_sound (row 18 116) 18 116 hvalid hfast

theorem strict_r18_part117 : ∀ i ∈ List.range 1, StrictCheckAt 18 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 117) 18 117 := by decide +kernel
  exact strictAtFast_sound (row 18 117) 18 117 hvalid hfast

theorem strict_r18_part118 : ∀ i ∈ List.range 1, StrictCheckAt 18 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 118) 18 118 := by decide +kernel
  exact strictAtFast_sound (row 18 118) 18 118 hvalid hfast

theorem strict_r18_part119 : ∀ i ∈ List.range 1, StrictCheckAt 18 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 119) 18 119 := by decide +kernel
  exact strictAtFast_sound (row 18 119) 18 119 hvalid hfast

theorem strict_r18_part120 : ∀ i ∈ List.range 1, StrictCheckAt 18 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 120) 18 120 := by decide +kernel
  exact strictAtFast_sound (row 18 120) 18 120 hvalid hfast

theorem strict_r18_part121 : ∀ i ∈ List.range 1, StrictCheckAt 18 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 121 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 121) 18 121 := by decide +kernel
  exact strictAtFast_sound (row 18 121) 18 121 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
