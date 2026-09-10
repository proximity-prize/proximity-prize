import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r27_part80 : ∀ i ∈ List.range 1, StrictCheckAt 27 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 80) 27 80 := by decide +kernel
  exact strictAtFast_sound (row 27 80) 27 80 hvalid hfast

theorem strict_r27_part81 : ∀ i ∈ List.range 1, StrictCheckAt 27 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 81) 27 81 := by decide +kernel
  exact strictAtFast_sound (row 27 81) 27 81 hvalid hfast

theorem strict_r27_part82 : ∀ i ∈ List.range 1, StrictCheckAt 27 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 82) 27 82 := by decide +kernel
  exact strictAtFast_sound (row 27 82) 27 82 hvalid hfast

theorem strict_r27_part83 : ∀ i ∈ List.range 1, StrictCheckAt 27 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 83) 27 83 := by decide +kernel
  exact strictAtFast_sound (row 27 83) 27 83 hvalid hfast

theorem strict_r27_part84 : ∀ i ∈ List.range 1, StrictCheckAt 27 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 84) 27 84 := by decide +kernel
  exact strictAtFast_sound (row 27 84) 27 84 hvalid hfast

theorem strict_r27_part85 : ∀ i ∈ List.range 1, StrictCheckAt 27 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 85) 27 85 := by decide +kernel
  exact strictAtFast_sound (row 27 85) 27 85 hvalid hfast

theorem strict_r27_part86 : ∀ i ∈ List.range 1, StrictCheckAt 27 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 86) 27 86 := by decide +kernel
  exact strictAtFast_sound (row 27 86) 27 86 hvalid hfast

theorem strict_r27_part87 : ∀ i ∈ List.range 1, StrictCheckAt 27 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 87) 27 87 := by decide +kernel
  exact strictAtFast_sound (row 27 87) 27 87 hvalid hfast

theorem strict_r27_part88 : ∀ i ∈ List.range 1, StrictCheckAt 27 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 88) 27 88 := by decide +kernel
  exact strictAtFast_sound (row 27 88) 27 88 hvalid hfast

theorem strict_r27_part89 : ∀ i ∈ List.range 1, StrictCheckAt 27 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 89) 27 89 := by decide +kernel
  exact strictAtFast_sound (row 27 89) 27 89 hvalid hfast

theorem strict_r27_part90 : ∀ i ∈ List.range 1, StrictCheckAt 27 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 90) 27 90 := by decide +kernel
  exact strictAtFast_sound (row 27 90) 27 90 hvalid hfast

theorem strict_r27_part91 : ∀ i ∈ List.range 1, StrictCheckAt 27 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 91) 27 91 := by decide +kernel
  exact strictAtFast_sound (row 27 91) 27 91 hvalid hfast

theorem strict_r27_part92 : ∀ i ∈ List.range 1, StrictCheckAt 27 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 92) 27 92 := by decide +kernel
  exact strictAtFast_sound (row 27 92) 27 92 hvalid hfast

theorem strict_r27_part93 : ∀ i ∈ List.range 1, StrictCheckAt 27 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 93) 27 93 := by decide +kernel
  exact strictAtFast_sound (row 27 93) 27 93 hvalid hfast

theorem strict_r27_part94 : ∀ i ∈ List.range 1, StrictCheckAt 27 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 94) 27 94 := by decide +kernel
  exact strictAtFast_sound (row 27 94) 27 94 hvalid hfast

theorem strict_r27_part95 : ∀ i ∈ List.range 1, StrictCheckAt 27 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 95) 27 95 := by decide +kernel
  exact strictAtFast_sound (row 27 95) 27 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
