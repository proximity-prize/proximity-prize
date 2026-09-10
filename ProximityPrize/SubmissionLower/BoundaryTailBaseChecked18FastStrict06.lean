import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r18_part80 : ∀ i ∈ List.range 1, StrictCheckAt 18 (80+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 80 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 80) 18 80 := by decide +kernel
  exact strictAtFast_sound (row 18 80) 18 80 hvalid hfast

theorem strict_r18_part81 : ∀ i ∈ List.range 1, StrictCheckAt 18 (81+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 81 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 81) 18 81 := by decide +kernel
  exact strictAtFast_sound (row 18 81) 18 81 hvalid hfast

theorem strict_r18_part82 : ∀ i ∈ List.range 1, StrictCheckAt 18 (82+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 82 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 82) 18 82 := by decide +kernel
  exact strictAtFast_sound (row 18 82) 18 82 hvalid hfast

theorem strict_r18_part83 : ∀ i ∈ List.range 1, StrictCheckAt 18 (83+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 83 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 83) 18 83 := by decide +kernel
  exact strictAtFast_sound (row 18 83) 18 83 hvalid hfast

theorem strict_r18_part84 : ∀ i ∈ List.range 1, StrictCheckAt 18 (84+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 84 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 84) 18 84 := by decide +kernel
  exact strictAtFast_sound (row 18 84) 18 84 hvalid hfast

theorem strict_r18_part85 : ∀ i ∈ List.range 1, StrictCheckAt 18 (85+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 85 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 85) 18 85 := by decide +kernel
  exact strictAtFast_sound (row 18 85) 18 85 hvalid hfast

theorem strict_r18_part86 : ∀ i ∈ List.range 1, StrictCheckAt 18 (86+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 86 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 86) 18 86 := by decide +kernel
  exact strictAtFast_sound (row 18 86) 18 86 hvalid hfast

theorem strict_r18_part87 : ∀ i ∈ List.range 1, StrictCheckAt 18 (87+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 87 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 87) 18 87 := by decide +kernel
  exact strictAtFast_sound (row 18 87) 18 87 hvalid hfast

theorem strict_r18_part88 : ∀ i ∈ List.range 1, StrictCheckAt 18 (88+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 88 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 88) 18 88 := by decide +kernel
  exact strictAtFast_sound (row 18 88) 18 88 hvalid hfast

theorem strict_r18_part89 : ∀ i ∈ List.range 1, StrictCheckAt 18 (89+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 89 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 89) 18 89 := by decide +kernel
  exact strictAtFast_sound (row 18 89) 18 89 hvalid hfast

theorem strict_r18_part90 : ∀ i ∈ List.range 1, StrictCheckAt 18 (90+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 90 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 90) 18 90 := by decide +kernel
  exact strictAtFast_sound (row 18 90) 18 90 hvalid hfast

theorem strict_r18_part91 : ∀ i ∈ List.range 1, StrictCheckAt 18 (91+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 91 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 91) 18 91 := by decide +kernel
  exact strictAtFast_sound (row 18 91) 18 91 hvalid hfast

theorem strict_r18_part92 : ∀ i ∈ List.range 1, StrictCheckAt 18 (92+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 92 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 92) 18 92 := by decide +kernel
  exact strictAtFast_sound (row 18 92) 18 92 hvalid hfast

theorem strict_r18_part93 : ∀ i ∈ List.range 1, StrictCheckAt 18 (93+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 93 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 93) 18 93 := by decide +kernel
  exact strictAtFast_sound (row 18 93) 18 93 hvalid hfast

theorem strict_r18_part94 : ∀ i ∈ List.range 1, StrictCheckAt 18 (94+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 94 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 94) 18 94 := by decide +kernel
  exact strictAtFast_sound (row 18 94) 18 94 hvalid hfast

theorem strict_r18_part95 : ∀ i ∈ List.range 1, StrictCheckAt 18 (95+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 95 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 95) 18 95 := by decide +kernel
  exact strictAtFast_sound (row 18 95) 18 95 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
