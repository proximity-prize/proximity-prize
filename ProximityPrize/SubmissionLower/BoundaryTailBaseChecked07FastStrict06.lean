import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r7_part80 : ∀ i ∈ List.range 1, StrictCheckAt 7 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 80) 7 80 := by decide +kernel
  exact strictAtFast_sound (row 7 80) 7 80 hvalid hfast

theorem strict_r7_part81 : ∀ i ∈ List.range 1, StrictCheckAt 7 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 81) 7 81 := by decide +kernel
  exact strictAtFast_sound (row 7 81) 7 81 hvalid hfast

theorem strict_r7_part82 : ∀ i ∈ List.range 1, StrictCheckAt 7 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 82) 7 82 := by decide +kernel
  exact strictAtFast_sound (row 7 82) 7 82 hvalid hfast

theorem strict_r7_part83 : ∀ i ∈ List.range 1, StrictCheckAt 7 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 83) 7 83 := by decide +kernel
  exact strictAtFast_sound (row 7 83) 7 83 hvalid hfast

theorem strict_r7_part84 : ∀ i ∈ List.range 1, StrictCheckAt 7 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 84) 7 84 := by decide +kernel
  exact strictAtFast_sound (row 7 84) 7 84 hvalid hfast

theorem strict_r7_part85 : ∀ i ∈ List.range 1, StrictCheckAt 7 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 85) 7 85 := by decide +kernel
  exact strictAtFast_sound (row 7 85) 7 85 hvalid hfast

theorem strict_r7_part86 : ∀ i ∈ List.range 1, StrictCheckAt 7 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 86) 7 86 := by decide +kernel
  exact strictAtFast_sound (row 7 86) 7 86 hvalid hfast

theorem strict_r7_part87 : ∀ i ∈ List.range 1, StrictCheckAt 7 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 87) 7 87 := by decide +kernel
  exact strictAtFast_sound (row 7 87) 7 87 hvalid hfast

theorem strict_r7_part88 : ∀ i ∈ List.range 1, StrictCheckAt 7 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 88) 7 88 := by decide +kernel
  exact strictAtFast_sound (row 7 88) 7 88 hvalid hfast

theorem strict_r7_part89 : ∀ i ∈ List.range 1, StrictCheckAt 7 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 89) 7 89 := by decide +kernel
  exact strictAtFast_sound (row 7 89) 7 89 hvalid hfast

theorem strict_r7_part90 : ∀ i ∈ List.range 1, StrictCheckAt 7 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 90) 7 90 := by decide +kernel
  exact strictAtFast_sound (row 7 90) 7 90 hvalid hfast

theorem strict_r7_part91 : ∀ i ∈ List.range 1, StrictCheckAt 7 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 91) 7 91 := by decide +kernel
  exact strictAtFast_sound (row 7 91) 7 91 hvalid hfast

theorem strict_r7_part92 : ∀ i ∈ List.range 1, StrictCheckAt 7 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 92) 7 92 := by decide +kernel
  exact strictAtFast_sound (row 7 92) 7 92 hvalid hfast

theorem strict_r7_part93 : ∀ i ∈ List.range 1, StrictCheckAt 7 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 93) 7 93 := by decide +kernel
  exact strictAtFast_sound (row 7 93) 7 93 hvalid hfast

theorem strict_r7_part94 : ∀ i ∈ List.range 1, StrictCheckAt 7 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 94) 7 94 := by decide +kernel
  exact strictAtFast_sound (row 7 94) 7 94 hvalid hfast

theorem strict_r7_part95 : ∀ i ∈ List.range 1, StrictCheckAt 7 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 95) 7 95 := by decide +kernel
  exact strictAtFast_sound (row 7 95) 7 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
