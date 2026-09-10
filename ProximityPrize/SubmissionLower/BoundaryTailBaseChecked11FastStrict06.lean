import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r11_part80 : ∀ i ∈ List.range 1, StrictCheckAt 11 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 80) 11 80 := by decide +kernel
  exact strictAtFast_sound (row 11 80) 11 80 hvalid hfast

theorem strict_r11_part81 : ∀ i ∈ List.range 1, StrictCheckAt 11 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 81) 11 81 := by decide +kernel
  exact strictAtFast_sound (row 11 81) 11 81 hvalid hfast

theorem strict_r11_part82 : ∀ i ∈ List.range 1, StrictCheckAt 11 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 82) 11 82 := by decide +kernel
  exact strictAtFast_sound (row 11 82) 11 82 hvalid hfast

theorem strict_r11_part83 : ∀ i ∈ List.range 1, StrictCheckAt 11 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 83) 11 83 := by decide +kernel
  exact strictAtFast_sound (row 11 83) 11 83 hvalid hfast

theorem strict_r11_part84 : ∀ i ∈ List.range 1, StrictCheckAt 11 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 84) 11 84 := by decide +kernel
  exact strictAtFast_sound (row 11 84) 11 84 hvalid hfast

theorem strict_r11_part85 : ∀ i ∈ List.range 1, StrictCheckAt 11 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 85) 11 85 := by decide +kernel
  exact strictAtFast_sound (row 11 85) 11 85 hvalid hfast

theorem strict_r11_part86 : ∀ i ∈ List.range 1, StrictCheckAt 11 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 86) 11 86 := by decide +kernel
  exact strictAtFast_sound (row 11 86) 11 86 hvalid hfast

theorem strict_r11_part87 : ∀ i ∈ List.range 1, StrictCheckAt 11 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 87) 11 87 := by decide +kernel
  exact strictAtFast_sound (row 11 87) 11 87 hvalid hfast

theorem strict_r11_part88 : ∀ i ∈ List.range 1, StrictCheckAt 11 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 88) 11 88 := by decide +kernel
  exact strictAtFast_sound (row 11 88) 11 88 hvalid hfast

theorem strict_r11_part89 : ∀ i ∈ List.range 1, StrictCheckAt 11 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 89) 11 89 := by decide +kernel
  exact strictAtFast_sound (row 11 89) 11 89 hvalid hfast

theorem strict_r11_part90 : ∀ i ∈ List.range 1, StrictCheckAt 11 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 90) 11 90 := by decide +kernel
  exact strictAtFast_sound (row 11 90) 11 90 hvalid hfast

theorem strict_r11_part91 : ∀ i ∈ List.range 1, StrictCheckAt 11 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 91) 11 91 := by decide +kernel
  exact strictAtFast_sound (row 11 91) 11 91 hvalid hfast

theorem strict_r11_part92 : ∀ i ∈ List.range 1, StrictCheckAt 11 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 92) 11 92 := by decide +kernel
  exact strictAtFast_sound (row 11 92) 11 92 hvalid hfast

theorem strict_r11_part93 : ∀ i ∈ List.range 1, StrictCheckAt 11 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 93) 11 93 := by decide +kernel
  exact strictAtFast_sound (row 11 93) 11 93 hvalid hfast

theorem strict_r11_part94 : ∀ i ∈ List.range 1, StrictCheckAt 11 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 94) 11 94 := by decide +kernel
  exact strictAtFast_sound (row 11 94) 11 94 hvalid hfast

theorem strict_r11_part95 : ∀ i ∈ List.range 1, StrictCheckAt 11 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 95) 11 95 := by decide +kernel
  exact strictAtFast_sound (row 11 95) 11 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
