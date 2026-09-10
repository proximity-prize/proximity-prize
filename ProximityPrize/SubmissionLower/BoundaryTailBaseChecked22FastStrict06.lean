import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r22_part80 : ∀ i ∈ List.range 1, StrictCheckAt 22 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 80) 22 80 := by decide +kernel
  exact strictAtFast_sound (row 22 80) 22 80 hvalid hfast

theorem strict_r22_part81 : ∀ i ∈ List.range 1, StrictCheckAt 22 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 81) 22 81 := by decide +kernel
  exact strictAtFast_sound (row 22 81) 22 81 hvalid hfast

theorem strict_r22_part82 : ∀ i ∈ List.range 1, StrictCheckAt 22 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 82) 22 82 := by decide +kernel
  exact strictAtFast_sound (row 22 82) 22 82 hvalid hfast

theorem strict_r22_part83 : ∀ i ∈ List.range 1, StrictCheckAt 22 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 83) 22 83 := by decide +kernel
  exact strictAtFast_sound (row 22 83) 22 83 hvalid hfast

theorem strict_r22_part84 : ∀ i ∈ List.range 1, StrictCheckAt 22 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 84) 22 84 := by decide +kernel
  exact strictAtFast_sound (row 22 84) 22 84 hvalid hfast

theorem strict_r22_part85 : ∀ i ∈ List.range 1, StrictCheckAt 22 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 85) 22 85 := by decide +kernel
  exact strictAtFast_sound (row 22 85) 22 85 hvalid hfast

theorem strict_r22_part86 : ∀ i ∈ List.range 1, StrictCheckAt 22 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 86) 22 86 := by decide +kernel
  exact strictAtFast_sound (row 22 86) 22 86 hvalid hfast

theorem strict_r22_part87 : ∀ i ∈ List.range 1, StrictCheckAt 22 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 87) 22 87 := by decide +kernel
  exact strictAtFast_sound (row 22 87) 22 87 hvalid hfast

theorem strict_r22_part88 : ∀ i ∈ List.range 1, StrictCheckAt 22 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 88) 22 88 := by decide +kernel
  exact strictAtFast_sound (row 22 88) 22 88 hvalid hfast

theorem strict_r22_part89 : ∀ i ∈ List.range 1, StrictCheckAt 22 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 89) 22 89 := by decide +kernel
  exact strictAtFast_sound (row 22 89) 22 89 hvalid hfast

theorem strict_r22_part90 : ∀ i ∈ List.range 1, StrictCheckAt 22 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 90) 22 90 := by decide +kernel
  exact strictAtFast_sound (row 22 90) 22 90 hvalid hfast

theorem strict_r22_part91 : ∀ i ∈ List.range 1, StrictCheckAt 22 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 91) 22 91 := by decide +kernel
  exact strictAtFast_sound (row 22 91) 22 91 hvalid hfast

theorem strict_r22_part92 : ∀ i ∈ List.range 1, StrictCheckAt 22 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 92) 22 92 := by decide +kernel
  exact strictAtFast_sound (row 22 92) 22 92 hvalid hfast

theorem strict_r22_part93 : ∀ i ∈ List.range 1, StrictCheckAt 22 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 93) 22 93 := by decide +kernel
  exact strictAtFast_sound (row 22 93) 22 93 hvalid hfast

theorem strict_r22_part94 : ∀ i ∈ List.range 1, StrictCheckAt 22 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 94) 22 94 := by decide +kernel
  exact strictAtFast_sound (row 22 94) 22 94 hvalid hfast

theorem strict_r22_part95 : ∀ i ∈ List.range 1, StrictCheckAt 22 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 95) 22 95 := by decide +kernel
  exact strictAtFast_sound (row 22 95) 22 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
