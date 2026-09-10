import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r17_part112 : ∀ i ∈ List.range 1, StrictCheckAt 17 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 112) 17 112 := by decide +kernel
  exact strictAtFast_sound (row 17 112) 17 112 hvalid hfast

theorem strict_r17_part113 : ∀ i ∈ List.range 1, StrictCheckAt 17 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 113) 17 113 := by decide +kernel
  exact strictAtFast_sound (row 17 113) 17 113 hvalid hfast

theorem strict_r17_part114 : ∀ i ∈ List.range 1, StrictCheckAt 17 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 114) 17 114 := by decide +kernel
  exact strictAtFast_sound (row 17 114) 17 114 hvalid hfast

theorem strict_r17_part115 : ∀ i ∈ List.range 1, StrictCheckAt 17 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 115) 17 115 := by decide +kernel
  exact strictAtFast_sound (row 17 115) 17 115 hvalid hfast

theorem strict_r17_part116 : ∀ i ∈ List.range 1, StrictCheckAt 17 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 116) 17 116 := by decide +kernel
  exact strictAtFast_sound (row 17 116) 17 116 hvalid hfast

theorem strict_r17_part117 : ∀ i ∈ List.range 1, StrictCheckAt 17 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 117) 17 117 := by decide +kernel
  exact strictAtFast_sound (row 17 117) 17 117 hvalid hfast

theorem strict_r17_part118 : ∀ i ∈ List.range 1, StrictCheckAt 17 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 118) 17 118 := by decide +kernel
  exact strictAtFast_sound (row 17 118) 17 118 hvalid hfast

theorem strict_r17_part119 : ∀ i ∈ List.range 1, StrictCheckAt 17 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 119) 17 119 := by decide +kernel
  exact strictAtFast_sound (row 17 119) 17 119 hvalid hfast

theorem strict_r17_part120 : ∀ i ∈ List.range 1, StrictCheckAt 17 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 120) 17 120 := by decide +kernel
  exact strictAtFast_sound (row 17 120) 17 120 hvalid hfast

theorem strict_r17_part121 : ∀ i ∈ List.range 1, StrictCheckAt 17 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 121 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 121) 17 121 := by decide +kernel
  exact strictAtFast_sound (row 17 121) 17 121 hvalid hfast

theorem strict_r17_part122 : ∀ i ∈ List.range 1, StrictCheckAt 17 (122+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 122 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 122) 17 122 := by decide +kernel
  exact strictAtFast_sound (row 17 122) 17 122 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
