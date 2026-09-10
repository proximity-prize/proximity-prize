import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r12_part112 : ∀ i ∈ List.range 1, StrictCheckAt 12 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 112) 12 112 := by decide +kernel
  exact strictAtFast_sound (row 12 112) 12 112 hvalid hfast

theorem strict_r12_part113 : ∀ i ∈ List.range 1, StrictCheckAt 12 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 113) 12 113 := by decide +kernel
  exact strictAtFast_sound (row 12 113) 12 113 hvalid hfast

theorem strict_r12_part114 : ∀ i ∈ List.range 1, StrictCheckAt 12 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 114) 12 114 := by decide +kernel
  exact strictAtFast_sound (row 12 114) 12 114 hvalid hfast

theorem strict_r12_part115 : ∀ i ∈ List.range 1, StrictCheckAt 12 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 115) 12 115 := by decide +kernel
  exact strictAtFast_sound (row 12 115) 12 115 hvalid hfast

theorem strict_r12_part116 : ∀ i ∈ List.range 1, StrictCheckAt 12 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 116) 12 116 := by decide +kernel
  exact strictAtFast_sound (row 12 116) 12 116 hvalid hfast

theorem strict_r12_part117 : ∀ i ∈ List.range 1, StrictCheckAt 12 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 117) 12 117 := by decide +kernel
  exact strictAtFast_sound (row 12 117) 12 117 hvalid hfast

theorem strict_r12_part118 : ∀ i ∈ List.range 1, StrictCheckAt 12 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 118) 12 118 := by decide +kernel
  exact strictAtFast_sound (row 12 118) 12 118 hvalid hfast

theorem strict_r12_part119 : ∀ i ∈ List.range 1, StrictCheckAt 12 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 119) 12 119 := by decide +kernel
  exact strictAtFast_sound (row 12 119) 12 119 hvalid hfast

theorem strict_r12_part120 : ∀ i ∈ List.range 1, StrictCheckAt 12 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 120) 12 120 := by decide +kernel
  exact strictAtFast_sound (row 12 120) 12 120 hvalid hfast

theorem strict_r12_part121 : ∀ i ∈ List.range 1, StrictCheckAt 12 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 121 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 121) 12 121 := by decide +kernel
  exact strictAtFast_sound (row 12 121) 12 121 hvalid hfast

theorem strict_r12_part122 : ∀ i ∈ List.range 1, StrictCheckAt 12 (122+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 122 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 122) 12 122 := by decide +kernel
  exact strictAtFast_sound (row 12 122) 12 122 hvalid hfast

theorem strict_r12_part123 : ∀ i ∈ List.range 1, StrictCheckAt 12 (123+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 123 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 123) 12 123 := by decide +kernel
  exact strictAtFast_sound (row 12 123) 12 123 hvalid hfast

theorem strict_r12_part124 : ∀ i ∈ List.range 1, StrictCheckAt 12 (124+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 124 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 124) 12 124 := by decide +kernel
  exact strictAtFast_sound (row 12 124) 12 124 hvalid hfast

theorem strict_r12_part125 : ∀ i ∈ List.range 1, StrictCheckAt 12 (125+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 125 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 125) 12 125 := by decide +kernel
  exact strictAtFast_sound (row 12 125) 12 125 hvalid hfast

theorem strict_r12_part126 : ∀ i ∈ List.range 1, StrictCheckAt 12 (126+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 126 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 126) 12 126 := by decide +kernel
  exact strictAtFast_sound (row 12 126) 12 126 hvalid hfast

theorem strict_r12_part127 : ∀ i ∈ List.range 1, StrictCheckAt 12 (127+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 127 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 127) 12 127 := by decide +kernel
  exact strictAtFast_sound (row 12 127) 12 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
