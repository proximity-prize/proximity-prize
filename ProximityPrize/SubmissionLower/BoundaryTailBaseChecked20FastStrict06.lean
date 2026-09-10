import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r20_part80 : ∀ i ∈ List.range 1, StrictCheckAt 20 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 80) 20 80 := by decide +kernel
  exact strictAtFast_sound (row 20 80) 20 80 hvalid hfast

theorem strict_r20_part81 : ∀ i ∈ List.range 1, StrictCheckAt 20 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 81) 20 81 := by decide +kernel
  exact strictAtFast_sound (row 20 81) 20 81 hvalid hfast

theorem strict_r20_part82 : ∀ i ∈ List.range 1, StrictCheckAt 20 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 82) 20 82 := by decide +kernel
  exact strictAtFast_sound (row 20 82) 20 82 hvalid hfast

theorem strict_r20_part83 : ∀ i ∈ List.range 1, StrictCheckAt 20 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 83) 20 83 := by decide +kernel
  exact strictAtFast_sound (row 20 83) 20 83 hvalid hfast

theorem strict_r20_part84 : ∀ i ∈ List.range 1, StrictCheckAt 20 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 84) 20 84 := by decide +kernel
  exact strictAtFast_sound (row 20 84) 20 84 hvalid hfast

theorem strict_r20_part85 : ∀ i ∈ List.range 1, StrictCheckAt 20 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 85) 20 85 := by decide +kernel
  exact strictAtFast_sound (row 20 85) 20 85 hvalid hfast

theorem strict_r20_part86 : ∀ i ∈ List.range 1, StrictCheckAt 20 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 86) 20 86 := by decide +kernel
  exact strictAtFast_sound (row 20 86) 20 86 hvalid hfast

theorem strict_r20_part87 : ∀ i ∈ List.range 1, StrictCheckAt 20 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 87) 20 87 := by decide +kernel
  exact strictAtFast_sound (row 20 87) 20 87 hvalid hfast

theorem strict_r20_part88 : ∀ i ∈ List.range 1, StrictCheckAt 20 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 88) 20 88 := by decide +kernel
  exact strictAtFast_sound (row 20 88) 20 88 hvalid hfast

theorem strict_r20_part89 : ∀ i ∈ List.range 1, StrictCheckAt 20 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 89) 20 89 := by decide +kernel
  exact strictAtFast_sound (row 20 89) 20 89 hvalid hfast

theorem strict_r20_part90 : ∀ i ∈ List.range 1, StrictCheckAt 20 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 90) 20 90 := by decide +kernel
  exact strictAtFast_sound (row 20 90) 20 90 hvalid hfast

theorem strict_r20_part91 : ∀ i ∈ List.range 1, StrictCheckAt 20 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 91) 20 91 := by decide +kernel
  exact strictAtFast_sound (row 20 91) 20 91 hvalid hfast

theorem strict_r20_part92 : ∀ i ∈ List.range 1, StrictCheckAt 20 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 92) 20 92 := by decide +kernel
  exact strictAtFast_sound (row 20 92) 20 92 hvalid hfast

theorem strict_r20_part93 : ∀ i ∈ List.range 1, StrictCheckAt 20 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 93) 20 93 := by decide +kernel
  exact strictAtFast_sound (row 20 93) 20 93 hvalid hfast

theorem strict_r20_part94 : ∀ i ∈ List.range 1, StrictCheckAt 20 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 94) 20 94 := by decide +kernel
  exact strictAtFast_sound (row 20 94) 20 94 hvalid hfast

theorem strict_r20_part95 : ∀ i ∈ List.range 1, StrictCheckAt 20 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 95) 20 95 := by decide +kernel
  exact strictAtFast_sound (row 20 95) 20 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
