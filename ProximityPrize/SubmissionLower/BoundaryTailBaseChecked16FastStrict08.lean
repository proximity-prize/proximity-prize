import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r16_part112 : ∀ i ∈ List.range 1, StrictCheckAt 16 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 112) 16 112 := by decide +kernel
  exact strictAtFast_sound (row 16 112) 16 112 hvalid hfast

theorem strict_r16_part113 : ∀ i ∈ List.range 1, StrictCheckAt 16 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 113) 16 113 := by decide +kernel
  exact strictAtFast_sound (row 16 113) 16 113 hvalid hfast

theorem strict_r16_part114 : ∀ i ∈ List.range 1, StrictCheckAt 16 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 114) 16 114 := by decide +kernel
  exact strictAtFast_sound (row 16 114) 16 114 hvalid hfast

theorem strict_r16_part115 : ∀ i ∈ List.range 1, StrictCheckAt 16 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 115) 16 115 := by decide +kernel
  exact strictAtFast_sound (row 16 115) 16 115 hvalid hfast

theorem strict_r16_part116 : ∀ i ∈ List.range 1, StrictCheckAt 16 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 116) 16 116 := by decide +kernel
  exact strictAtFast_sound (row 16 116) 16 116 hvalid hfast

theorem strict_r16_part117 : ∀ i ∈ List.range 1, StrictCheckAt 16 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 117) 16 117 := by decide +kernel
  exact strictAtFast_sound (row 16 117) 16 117 hvalid hfast

theorem strict_r16_part118 : ∀ i ∈ List.range 1, StrictCheckAt 16 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 118) 16 118 := by decide +kernel
  exact strictAtFast_sound (row 16 118) 16 118 hvalid hfast

theorem strict_r16_part119 : ∀ i ∈ List.range 1, StrictCheckAt 16 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 119) 16 119 := by decide +kernel
  exact strictAtFast_sound (row 16 119) 16 119 hvalid hfast

theorem strict_r16_part120 : ∀ i ∈ List.range 1, StrictCheckAt 16 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 120) 16 120 := by decide +kernel
  exact strictAtFast_sound (row 16 120) 16 120 hvalid hfast

theorem strict_r16_part121 : ∀ i ∈ List.range 1, StrictCheckAt 16 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 121 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 121) 16 121 := by decide +kernel
  exact strictAtFast_sound (row 16 121) 16 121 hvalid hfast

theorem strict_r16_part122 : ∀ i ∈ List.range 1, StrictCheckAt 16 (122+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 122 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 122) 16 122 := by decide +kernel
  exact strictAtFast_sound (row 16 122) 16 122 hvalid hfast

theorem strict_r16_part123 : ∀ i ∈ List.range 1, StrictCheckAt 16 (123+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 123 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 123) 16 123 := by decide +kernel
  exact strictAtFast_sound (row 16 123) 16 123 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
