import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r11_part112 : ∀ i ∈ List.range 1, StrictCheckAt 11 (112+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 112 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 112) 11 112 := by decide +kernel
  exact strictAtFast_sound (row 11 112) 11 112 hvalid hfast

theorem strict_r11_part113 : ∀ i ∈ List.range 1, StrictCheckAt 11 (113+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 113 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 113) 11 113 := by decide +kernel
  exact strictAtFast_sound (row 11 113) 11 113 hvalid hfast

theorem strict_r11_part114 : ∀ i ∈ List.range 1, StrictCheckAt 11 (114+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 114 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 114) 11 114 := by decide +kernel
  exact strictAtFast_sound (row 11 114) 11 114 hvalid hfast

theorem strict_r11_part115 : ∀ i ∈ List.range 1, StrictCheckAt 11 (115+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 115 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 115) 11 115 := by decide +kernel
  exact strictAtFast_sound (row 11 115) 11 115 hvalid hfast

theorem strict_r11_part116 : ∀ i ∈ List.range 1, StrictCheckAt 11 (116+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 116 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 116) 11 116 := by decide +kernel
  exact strictAtFast_sound (row 11 116) 11 116 hvalid hfast

theorem strict_r11_part117 : ∀ i ∈ List.range 1, StrictCheckAt 11 (117+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 117 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 117) 11 117 := by decide +kernel
  exact strictAtFast_sound (row 11 117) 11 117 hvalid hfast

theorem strict_r11_part118 : ∀ i ∈ List.range 1, StrictCheckAt 11 (118+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 118 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 118) 11 118 := by decide +kernel
  exact strictAtFast_sound (row 11 118) 11 118 hvalid hfast

theorem strict_r11_part119 : ∀ i ∈ List.range 1, StrictCheckAt 11 (119+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 119 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 119) 11 119 := by decide +kernel
  exact strictAtFast_sound (row 11 119) 11 119 hvalid hfast

theorem strict_r11_part120 : ∀ i ∈ List.range 1, StrictCheckAt 11 (120+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 120 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 120) 11 120 := by decide +kernel
  exact strictAtFast_sound (row 11 120) 11 120 hvalid hfast

theorem strict_r11_part121 : ∀ i ∈ List.range 1, StrictCheckAt 11 (121+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 121 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 121) 11 121 := by decide +kernel
  exact strictAtFast_sound (row 11 121) 11 121 hvalid hfast

theorem strict_r11_part122 : ∀ i ∈ List.range 1, StrictCheckAt 11 (122+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 122 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 122) 11 122 := by decide +kernel
  exact strictAtFast_sound (row 11 122) 11 122 hvalid hfast

theorem strict_r11_part123 : ∀ i ∈ List.range 1, StrictCheckAt 11 (123+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 123 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 123) 11 123 := by decide +kernel
  exact strictAtFast_sound (row 11 123) 11 123 hvalid hfast

theorem strict_r11_part124 : ∀ i ∈ List.range 1, StrictCheckAt 11 (124+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 124 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 124) 11 124 := by decide +kernel
  exact strictAtFast_sound (row 11 124) 11 124 hvalid hfast

theorem strict_r11_part125 : ∀ i ∈ List.range 1, StrictCheckAt 11 (125+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 125 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 125) 11 125 := by decide +kernel
  exact strictAtFast_sound (row 11 125) 11 125 hvalid hfast

theorem strict_r11_part126 : ∀ i ∈ List.range 1, StrictCheckAt 11 (126+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 126 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 126) 11 126 := by decide +kernel
  exact strictAtFast_sound (row 11 126) 11 126 hvalid hfast

theorem strict_r11_part127 : ∀ i ∈ List.range 1, StrictCheckAt 11 (127+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 127 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 127) 11 127 := by decide +kernel
  exact strictAtFast_sound (row 11 127) 11 127 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
