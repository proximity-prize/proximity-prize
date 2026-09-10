import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r8_part64 : ∀ i ∈ List.range 1, StrictCheckAt 8 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 64) 8 64 := by decide +kernel
  exact strictAtFast_sound (row 8 64) 8 64 hvalid hfast

theorem strict_r8_part65 : ∀ i ∈ List.range 1, StrictCheckAt 8 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 65) 8 65 := by decide +kernel
  exact strictAtFast_sound (row 8 65) 8 65 hvalid hfast

theorem strict_r8_part66 : ∀ i ∈ List.range 1, StrictCheckAt 8 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 66) 8 66 := by decide +kernel
  exact strictAtFast_sound (row 8 66) 8 66 hvalid hfast

theorem strict_r8_part67 : ∀ i ∈ List.range 1, StrictCheckAt 8 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 67) 8 67 := by decide +kernel
  exact strictAtFast_sound (row 8 67) 8 67 hvalid hfast

theorem strict_r8_part68 : ∀ i ∈ List.range 1, StrictCheckAt 8 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 68) 8 68 := by decide +kernel
  exact strictAtFast_sound (row 8 68) 8 68 hvalid hfast

theorem strict_r8_part69 : ∀ i ∈ List.range 1, StrictCheckAt 8 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 69) 8 69 := by decide +kernel
  exact strictAtFast_sound (row 8 69) 8 69 hvalid hfast

theorem strict_r8_part70 : ∀ i ∈ List.range 1, StrictCheckAt 8 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 70) 8 70 := by decide +kernel
  exact strictAtFast_sound (row 8 70) 8 70 hvalid hfast

theorem strict_r8_part71 : ∀ i ∈ List.range 1, StrictCheckAt 8 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 71) 8 71 := by decide +kernel
  exact strictAtFast_sound (row 8 71) 8 71 hvalid hfast

theorem strict_r8_part72 : ∀ i ∈ List.range 1, StrictCheckAt 8 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 72) 8 72 := by decide +kernel
  exact strictAtFast_sound (row 8 72) 8 72 hvalid hfast

theorem strict_r8_part73 : ∀ i ∈ List.range 1, StrictCheckAt 8 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 73) 8 73 := by decide +kernel
  exact strictAtFast_sound (row 8 73) 8 73 hvalid hfast

theorem strict_r8_part74 : ∀ i ∈ List.range 1, StrictCheckAt 8 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 74) 8 74 := by decide +kernel
  exact strictAtFast_sound (row 8 74) 8 74 hvalid hfast

theorem strict_r8_part75 : ∀ i ∈ List.range 1, StrictCheckAt 8 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 75) 8 75 := by decide +kernel
  exact strictAtFast_sound (row 8 75) 8 75 hvalid hfast

theorem strict_r8_part76 : ∀ i ∈ List.range 1, StrictCheckAt 8 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 76) 8 76 := by decide +kernel
  exact strictAtFast_sound (row 8 76) 8 76 hvalid hfast

theorem strict_r8_part77 : ∀ i ∈ List.range 1, StrictCheckAt 8 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 77) 8 77 := by decide +kernel
  exact strictAtFast_sound (row 8 77) 8 77 hvalid hfast

theorem strict_r8_part78 : ∀ i ∈ List.range 1, StrictCheckAt 8 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 78) 8 78 := by decide +kernel
  exact strictAtFast_sound (row 8 78) 8 78 hvalid hfast

theorem strict_r8_part79 : ∀ i ∈ List.range 1, StrictCheckAt 8 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 79) 8 79 := by decide +kernel
  exact strictAtFast_sound (row 8 79) 8 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
