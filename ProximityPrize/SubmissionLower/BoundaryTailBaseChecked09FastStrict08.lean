import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r9_part112 : ∀ i ∈ List.range 1, StrictCheckAt 9 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 112) 9 112 := by decide +kernel
  exact strictAtFast_sound (row 9 112) 9 112 hvalid hfast

theorem strict_r9_part113 : ∀ i ∈ List.range 1, StrictCheckAt 9 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 113) 9 113 := by decide +kernel
  exact strictAtFast_sound (row 9 113) 9 113 hvalid hfast

theorem strict_r9_part114 : ∀ i ∈ List.range 1, StrictCheckAt 9 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 114) 9 114 := by decide +kernel
  exact strictAtFast_sound (row 9 114) 9 114 hvalid hfast

theorem strict_r9_part115 : ∀ i ∈ List.range 1, StrictCheckAt 9 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 115) 9 115 := by decide +kernel
  exact strictAtFast_sound (row 9 115) 9 115 hvalid hfast

theorem strict_r9_part116 : ∀ i ∈ List.range 1, StrictCheckAt 9 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 116) 9 116 := by decide +kernel
  exact strictAtFast_sound (row 9 116) 9 116 hvalid hfast

theorem strict_r9_part117 : ∀ i ∈ List.range 1, StrictCheckAt 9 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 117) 9 117 := by decide +kernel
  exact strictAtFast_sound (row 9 117) 9 117 hvalid hfast

theorem strict_r9_part118 : ∀ i ∈ List.range 1, StrictCheckAt 9 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 118) 9 118 := by decide +kernel
  exact strictAtFast_sound (row 9 118) 9 118 hvalid hfast

theorem strict_r9_part119 : ∀ i ∈ List.range 1, StrictCheckAt 9 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 119) 9 119 := by decide +kernel
  exact strictAtFast_sound (row 9 119) 9 119 hvalid hfast

theorem strict_r9_part120 : ∀ i ∈ List.range 1, StrictCheckAt 9 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 120) 9 120 := by decide +kernel
  exact strictAtFast_sound (row 9 120) 9 120 hvalid hfast

theorem strict_r9_part121 : ∀ i ∈ List.range 1, StrictCheckAt 9 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 121 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 121) 9 121 := by decide +kernel
  exact strictAtFast_sound (row 9 121) 9 121 hvalid hfast

theorem strict_r9_part122 : ∀ i ∈ List.range 1, StrictCheckAt 9 (122+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 122 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 122) 9 122 := by decide +kernel
  exact strictAtFast_sound (row 9 122) 9 122 hvalid hfast

theorem strict_r9_part123 : ∀ i ∈ List.range 1, StrictCheckAt 9 (123+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 123 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 123) 9 123 := by decide +kernel
  exact strictAtFast_sound (row 9 123) 9 123 hvalid hfast

theorem strict_r9_part124 : ∀ i ∈ List.range 1, StrictCheckAt 9 (124+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 124 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 124) 9 124 := by decide +kernel
  exact strictAtFast_sound (row 9 124) 9 124 hvalid hfast

theorem strict_r9_part125 : ∀ i ∈ List.range 1, StrictCheckAt 9 (125+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 125 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 125) 9 125 := by decide +kernel
  exact strictAtFast_sound (row 9 125) 9 125 hvalid hfast

theorem strict_r9_part126 : ∀ i ∈ List.range 1, StrictCheckAt 9 (126+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 126 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 126) 9 126 := by decide +kernel
  exact strictAtFast_sound (row 9 126) 9 126 hvalid hfast

theorem strict_r9_part127 : ∀ i ∈ List.range 1, StrictCheckAt 9 (127+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 9 127 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 9 127) 9 127 := by decide +kernel
  exact strictAtFast_sound (row 9 127) 9 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
