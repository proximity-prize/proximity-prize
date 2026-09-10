import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r12_part80 : ∀ i ∈ List.range 1, StrictCheckAt 12 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 80) 12 80 := by decide +kernel
  exact strictAtFast_sound (row 12 80) 12 80 hvalid hfast

theorem strict_r12_part81 : ∀ i ∈ List.range 1, StrictCheckAt 12 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 81) 12 81 := by decide +kernel
  exact strictAtFast_sound (row 12 81) 12 81 hvalid hfast

theorem strict_r12_part82 : ∀ i ∈ List.range 1, StrictCheckAt 12 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 82) 12 82 := by decide +kernel
  exact strictAtFast_sound (row 12 82) 12 82 hvalid hfast

theorem strict_r12_part83 : ∀ i ∈ List.range 1, StrictCheckAt 12 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 83) 12 83 := by decide +kernel
  exact strictAtFast_sound (row 12 83) 12 83 hvalid hfast

theorem strict_r12_part84 : ∀ i ∈ List.range 1, StrictCheckAt 12 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 84) 12 84 := by decide +kernel
  exact strictAtFast_sound (row 12 84) 12 84 hvalid hfast

theorem strict_r12_part85 : ∀ i ∈ List.range 1, StrictCheckAt 12 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 85) 12 85 := by decide +kernel
  exact strictAtFast_sound (row 12 85) 12 85 hvalid hfast

theorem strict_r12_part86 : ∀ i ∈ List.range 1, StrictCheckAt 12 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 86) 12 86 := by decide +kernel
  exact strictAtFast_sound (row 12 86) 12 86 hvalid hfast

theorem strict_r12_part87 : ∀ i ∈ List.range 1, StrictCheckAt 12 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 87) 12 87 := by decide +kernel
  exact strictAtFast_sound (row 12 87) 12 87 hvalid hfast

theorem strict_r12_part88 : ∀ i ∈ List.range 1, StrictCheckAt 12 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 88) 12 88 := by decide +kernel
  exact strictAtFast_sound (row 12 88) 12 88 hvalid hfast

theorem strict_r12_part89 : ∀ i ∈ List.range 1, StrictCheckAt 12 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 89) 12 89 := by decide +kernel
  exact strictAtFast_sound (row 12 89) 12 89 hvalid hfast

theorem strict_r12_part90 : ∀ i ∈ List.range 1, StrictCheckAt 12 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 90) 12 90 := by decide +kernel
  exact strictAtFast_sound (row 12 90) 12 90 hvalid hfast

theorem strict_r12_part91 : ∀ i ∈ List.range 1, StrictCheckAt 12 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 91) 12 91 := by decide +kernel
  exact strictAtFast_sound (row 12 91) 12 91 hvalid hfast

theorem strict_r12_part92 : ∀ i ∈ List.range 1, StrictCheckAt 12 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 92) 12 92 := by decide +kernel
  exact strictAtFast_sound (row 12 92) 12 92 hvalid hfast

theorem strict_r12_part93 : ∀ i ∈ List.range 1, StrictCheckAt 12 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 93) 12 93 := by decide +kernel
  exact strictAtFast_sound (row 12 93) 12 93 hvalid hfast

theorem strict_r12_part94 : ∀ i ∈ List.range 1, StrictCheckAt 12 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 94) 12 94 := by decide +kernel
  exact strictAtFast_sound (row 12 94) 12 94 hvalid hfast

theorem strict_r12_part95 : ∀ i ∈ List.range 1, StrictCheckAt 12 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 95) 12 95 := by decide +kernel
  exact strictAtFast_sound (row 12 95) 12 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
