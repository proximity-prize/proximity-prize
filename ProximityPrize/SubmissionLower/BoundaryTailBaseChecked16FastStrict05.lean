import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r16_part64 : ∀ i ∈ List.range 1, StrictCheckAt 16 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 64) 16 64 := by decide +kernel
  exact strictAtFast_sound (row 16 64) 16 64 hvalid hfast

theorem strict_r16_part65 : ∀ i ∈ List.range 1, StrictCheckAt 16 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 65) 16 65 := by decide +kernel
  exact strictAtFast_sound (row 16 65) 16 65 hvalid hfast

theorem strict_r16_part66 : ∀ i ∈ List.range 1, StrictCheckAt 16 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 66) 16 66 := by decide +kernel
  exact strictAtFast_sound (row 16 66) 16 66 hvalid hfast

theorem strict_r16_part67 : ∀ i ∈ List.range 1, StrictCheckAt 16 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 67) 16 67 := by decide +kernel
  exact strictAtFast_sound (row 16 67) 16 67 hvalid hfast

theorem strict_r16_part68 : ∀ i ∈ List.range 1, StrictCheckAt 16 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 68) 16 68 := by decide +kernel
  exact strictAtFast_sound (row 16 68) 16 68 hvalid hfast

theorem strict_r16_part69 : ∀ i ∈ List.range 1, StrictCheckAt 16 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 69) 16 69 := by decide +kernel
  exact strictAtFast_sound (row 16 69) 16 69 hvalid hfast

theorem strict_r16_part70 : ∀ i ∈ List.range 1, StrictCheckAt 16 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 70) 16 70 := by decide +kernel
  exact strictAtFast_sound (row 16 70) 16 70 hvalid hfast

theorem strict_r16_part71 : ∀ i ∈ List.range 1, StrictCheckAt 16 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 71) 16 71 := by decide +kernel
  exact strictAtFast_sound (row 16 71) 16 71 hvalid hfast

theorem strict_r16_part72 : ∀ i ∈ List.range 1, StrictCheckAt 16 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 72) 16 72 := by decide +kernel
  exact strictAtFast_sound (row 16 72) 16 72 hvalid hfast

theorem strict_r16_part73 : ∀ i ∈ List.range 1, StrictCheckAt 16 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 73) 16 73 := by decide +kernel
  exact strictAtFast_sound (row 16 73) 16 73 hvalid hfast

theorem strict_r16_part74 : ∀ i ∈ List.range 1, StrictCheckAt 16 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 74) 16 74 := by decide +kernel
  exact strictAtFast_sound (row 16 74) 16 74 hvalid hfast

theorem strict_r16_part75 : ∀ i ∈ List.range 1, StrictCheckAt 16 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 75) 16 75 := by decide +kernel
  exact strictAtFast_sound (row 16 75) 16 75 hvalid hfast

theorem strict_r16_part76 : ∀ i ∈ List.range 1, StrictCheckAt 16 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 76) 16 76 := by decide +kernel
  exact strictAtFast_sound (row 16 76) 16 76 hvalid hfast

theorem strict_r16_part77 : ∀ i ∈ List.range 1, StrictCheckAt 16 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 77) 16 77 := by decide +kernel
  exact strictAtFast_sound (row 16 77) 16 77 hvalid hfast

theorem strict_r16_part78 : ∀ i ∈ List.range 1, StrictCheckAt 16 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 78) 16 78 := by decide +kernel
  exact strictAtFast_sound (row 16 78) 16 78 hvalid hfast

theorem strict_r16_part79 : ∀ i ∈ List.range 1, StrictCheckAt 16 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 79) 16 79 := by decide +kernel
  exact strictAtFast_sound (row 16 79) 16 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
