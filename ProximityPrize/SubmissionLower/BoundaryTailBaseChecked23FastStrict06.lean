import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r23_part80 : ∀ i ∈ List.range 1, StrictCheckAt 23 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 80) 23 80 := by decide +kernel
  exact strictAtFast_sound (row 23 80) 23 80 hvalid hfast

theorem strict_r23_part81 : ∀ i ∈ List.range 1, StrictCheckAt 23 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 81) 23 81 := by decide +kernel
  exact strictAtFast_sound (row 23 81) 23 81 hvalid hfast

theorem strict_r23_part82 : ∀ i ∈ List.range 1, StrictCheckAt 23 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 82) 23 82 := by decide +kernel
  exact strictAtFast_sound (row 23 82) 23 82 hvalid hfast

theorem strict_r23_part83 : ∀ i ∈ List.range 1, StrictCheckAt 23 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 83) 23 83 := by decide +kernel
  exact strictAtFast_sound (row 23 83) 23 83 hvalid hfast

theorem strict_r23_part84 : ∀ i ∈ List.range 1, StrictCheckAt 23 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 84) 23 84 := by decide +kernel
  exact strictAtFast_sound (row 23 84) 23 84 hvalid hfast

theorem strict_r23_part85 : ∀ i ∈ List.range 1, StrictCheckAt 23 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 85) 23 85 := by decide +kernel
  exact strictAtFast_sound (row 23 85) 23 85 hvalid hfast

theorem strict_r23_part86 : ∀ i ∈ List.range 1, StrictCheckAt 23 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 86) 23 86 := by decide +kernel
  exact strictAtFast_sound (row 23 86) 23 86 hvalid hfast

theorem strict_r23_part87 : ∀ i ∈ List.range 1, StrictCheckAt 23 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 87) 23 87 := by decide +kernel
  exact strictAtFast_sound (row 23 87) 23 87 hvalid hfast

theorem strict_r23_part88 : ∀ i ∈ List.range 1, StrictCheckAt 23 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 88) 23 88 := by decide +kernel
  exact strictAtFast_sound (row 23 88) 23 88 hvalid hfast

theorem strict_r23_part89 : ∀ i ∈ List.range 1, StrictCheckAt 23 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 89) 23 89 := by decide +kernel
  exact strictAtFast_sound (row 23 89) 23 89 hvalid hfast

theorem strict_r23_part90 : ∀ i ∈ List.range 1, StrictCheckAt 23 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 90) 23 90 := by decide +kernel
  exact strictAtFast_sound (row 23 90) 23 90 hvalid hfast

theorem strict_r23_part91 : ∀ i ∈ List.range 1, StrictCheckAt 23 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 91) 23 91 := by decide +kernel
  exact strictAtFast_sound (row 23 91) 23 91 hvalid hfast

theorem strict_r23_part92 : ∀ i ∈ List.range 1, StrictCheckAt 23 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 92) 23 92 := by decide +kernel
  exact strictAtFast_sound (row 23 92) 23 92 hvalid hfast

theorem strict_r23_part93 : ∀ i ∈ List.range 1, StrictCheckAt 23 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 93) 23 93 := by decide +kernel
  exact strictAtFast_sound (row 23 93) 23 93 hvalid hfast

theorem strict_r23_part94 : ∀ i ∈ List.range 1, StrictCheckAt 23 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 94) 23 94 := by decide +kernel
  exact strictAtFast_sound (row 23 94) 23 94 hvalid hfast

theorem strict_r23_part95 : ∀ i ∈ List.range 1, StrictCheckAt 23 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 23 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 23 95) 23 95 := by decide +kernel
  exact strictAtFast_sound (row 23 95) 23 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
