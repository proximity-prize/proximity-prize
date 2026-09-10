import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r15_part112 : ∀ i ∈ List.range 1, StrictCheckAt 15 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 112) 15 112 := by decide +kernel
  exact strictAtFast_sound (row 15 112) 15 112 hvalid hfast

theorem strict_r15_part113 : ∀ i ∈ List.range 1, StrictCheckAt 15 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 113) 15 113 := by decide +kernel
  exact strictAtFast_sound (row 15 113) 15 113 hvalid hfast

theorem strict_r15_part114 : ∀ i ∈ List.range 1, StrictCheckAt 15 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 114) 15 114 := by decide +kernel
  exact strictAtFast_sound (row 15 114) 15 114 hvalid hfast

theorem strict_r15_part115 : ∀ i ∈ List.range 1, StrictCheckAt 15 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 115) 15 115 := by decide +kernel
  exact strictAtFast_sound (row 15 115) 15 115 hvalid hfast

theorem strict_r15_part116 : ∀ i ∈ List.range 1, StrictCheckAt 15 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 116) 15 116 := by decide +kernel
  exact strictAtFast_sound (row 15 116) 15 116 hvalid hfast

theorem strict_r15_part117 : ∀ i ∈ List.range 1, StrictCheckAt 15 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 117) 15 117 := by decide +kernel
  exact strictAtFast_sound (row 15 117) 15 117 hvalid hfast

theorem strict_r15_part118 : ∀ i ∈ List.range 1, StrictCheckAt 15 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 118) 15 118 := by decide +kernel
  exact strictAtFast_sound (row 15 118) 15 118 hvalid hfast

theorem strict_r15_part119 : ∀ i ∈ List.range 1, StrictCheckAt 15 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 119) 15 119 := by decide +kernel
  exact strictAtFast_sound (row 15 119) 15 119 hvalid hfast

theorem strict_r15_part120 : ∀ i ∈ List.range 1, StrictCheckAt 15 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 120) 15 120 := by decide +kernel
  exact strictAtFast_sound (row 15 120) 15 120 hvalid hfast

theorem strict_r15_part121 : ∀ i ∈ List.range 1, StrictCheckAt 15 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 121 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 121) 15 121 := by decide +kernel
  exact strictAtFast_sound (row 15 121) 15 121 hvalid hfast

theorem strict_r15_part122 : ∀ i ∈ List.range 1, StrictCheckAt 15 (122+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 122 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 122) 15 122 := by decide +kernel
  exact strictAtFast_sound (row 15 122) 15 122 hvalid hfast

theorem strict_r15_part123 : ∀ i ∈ List.range 1, StrictCheckAt 15 (123+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 123 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 123) 15 123 := by decide +kernel
  exact strictAtFast_sound (row 15 123) 15 123 hvalid hfast

theorem strict_r15_part124 : ∀ i ∈ List.range 1, StrictCheckAt 15 (124+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 124 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 124) 15 124 := by decide +kernel
  exact strictAtFast_sound (row 15 124) 15 124 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
