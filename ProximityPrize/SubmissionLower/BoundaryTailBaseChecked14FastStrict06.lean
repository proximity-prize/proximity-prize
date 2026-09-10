import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r14_part80 : ∀ i ∈ List.range 1, StrictCheckAt 14 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 80) 14 80 := by decide +kernel
  exact strictAtFast_sound (row 14 80) 14 80 hvalid hfast

theorem strict_r14_part81 : ∀ i ∈ List.range 1, StrictCheckAt 14 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 81) 14 81 := by decide +kernel
  exact strictAtFast_sound (row 14 81) 14 81 hvalid hfast

theorem strict_r14_part82 : ∀ i ∈ List.range 1, StrictCheckAt 14 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 82) 14 82 := by decide +kernel
  exact strictAtFast_sound (row 14 82) 14 82 hvalid hfast

theorem strict_r14_part83 : ∀ i ∈ List.range 1, StrictCheckAt 14 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 83) 14 83 := by decide +kernel
  exact strictAtFast_sound (row 14 83) 14 83 hvalid hfast

theorem strict_r14_part84 : ∀ i ∈ List.range 1, StrictCheckAt 14 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 84) 14 84 := by decide +kernel
  exact strictAtFast_sound (row 14 84) 14 84 hvalid hfast

theorem strict_r14_part85 : ∀ i ∈ List.range 1, StrictCheckAt 14 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 85) 14 85 := by decide +kernel
  exact strictAtFast_sound (row 14 85) 14 85 hvalid hfast

theorem strict_r14_part86 : ∀ i ∈ List.range 1, StrictCheckAt 14 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 86) 14 86 := by decide +kernel
  exact strictAtFast_sound (row 14 86) 14 86 hvalid hfast

theorem strict_r14_part87 : ∀ i ∈ List.range 1, StrictCheckAt 14 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 87) 14 87 := by decide +kernel
  exact strictAtFast_sound (row 14 87) 14 87 hvalid hfast

theorem strict_r14_part88 : ∀ i ∈ List.range 1, StrictCheckAt 14 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 88) 14 88 := by decide +kernel
  exact strictAtFast_sound (row 14 88) 14 88 hvalid hfast

theorem strict_r14_part89 : ∀ i ∈ List.range 1, StrictCheckAt 14 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 89) 14 89 := by decide +kernel
  exact strictAtFast_sound (row 14 89) 14 89 hvalid hfast

theorem strict_r14_part90 : ∀ i ∈ List.range 1, StrictCheckAt 14 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 90) 14 90 := by decide +kernel
  exact strictAtFast_sound (row 14 90) 14 90 hvalid hfast

theorem strict_r14_part91 : ∀ i ∈ List.range 1, StrictCheckAt 14 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 91) 14 91 := by decide +kernel
  exact strictAtFast_sound (row 14 91) 14 91 hvalid hfast

theorem strict_r14_part92 : ∀ i ∈ List.range 1, StrictCheckAt 14 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 92) 14 92 := by decide +kernel
  exact strictAtFast_sound (row 14 92) 14 92 hvalid hfast

theorem strict_r14_part93 : ∀ i ∈ List.range 1, StrictCheckAt 14 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 93) 14 93 := by decide +kernel
  exact strictAtFast_sound (row 14 93) 14 93 hvalid hfast

theorem strict_r14_part94 : ∀ i ∈ List.range 1, StrictCheckAt 14 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 94) 14 94 := by decide +kernel
  exact strictAtFast_sound (row 14 94) 14 94 hvalid hfast

theorem strict_r14_part95 : ∀ i ∈ List.range 1, StrictCheckAt 14 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 95) 14 95 := by decide +kernel
  exact strictAtFast_sound (row 14 95) 14 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
