import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r14_part64 : ∀ i ∈ List.range 1, StrictCheckAt 14 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 64) 14 64 := by decide +kernel
  exact strictAtFast_sound (row 14 64) 14 64 hvalid hfast

theorem strict_r14_part65 : ∀ i ∈ List.range 1, StrictCheckAt 14 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 65) 14 65 := by decide +kernel
  exact strictAtFast_sound (row 14 65) 14 65 hvalid hfast

theorem strict_r14_part66 : ∀ i ∈ List.range 1, StrictCheckAt 14 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 66) 14 66 := by decide +kernel
  exact strictAtFast_sound (row 14 66) 14 66 hvalid hfast

theorem strict_r14_part67 : ∀ i ∈ List.range 1, StrictCheckAt 14 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 67) 14 67 := by decide +kernel
  exact strictAtFast_sound (row 14 67) 14 67 hvalid hfast

theorem strict_r14_part68 : ∀ i ∈ List.range 1, StrictCheckAt 14 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 68) 14 68 := by decide +kernel
  exact strictAtFast_sound (row 14 68) 14 68 hvalid hfast

theorem strict_r14_part69 : ∀ i ∈ List.range 1, StrictCheckAt 14 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 69) 14 69 := by decide +kernel
  exact strictAtFast_sound (row 14 69) 14 69 hvalid hfast

theorem strict_r14_part70 : ∀ i ∈ List.range 1, StrictCheckAt 14 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 70) 14 70 := by decide +kernel
  exact strictAtFast_sound (row 14 70) 14 70 hvalid hfast

theorem strict_r14_part71 : ∀ i ∈ List.range 1, StrictCheckAt 14 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 71) 14 71 := by decide +kernel
  exact strictAtFast_sound (row 14 71) 14 71 hvalid hfast

theorem strict_r14_part72 : ∀ i ∈ List.range 1, StrictCheckAt 14 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 72) 14 72 := by decide +kernel
  exact strictAtFast_sound (row 14 72) 14 72 hvalid hfast

theorem strict_r14_part73 : ∀ i ∈ List.range 1, StrictCheckAt 14 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 73) 14 73 := by decide +kernel
  exact strictAtFast_sound (row 14 73) 14 73 hvalid hfast

theorem strict_r14_part74 : ∀ i ∈ List.range 1, StrictCheckAt 14 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 74) 14 74 := by decide +kernel
  exact strictAtFast_sound (row 14 74) 14 74 hvalid hfast

theorem strict_r14_part75 : ∀ i ∈ List.range 1, StrictCheckAt 14 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 75) 14 75 := by decide +kernel
  exact strictAtFast_sound (row 14 75) 14 75 hvalid hfast

theorem strict_r14_part76 : ∀ i ∈ List.range 1, StrictCheckAt 14 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 76) 14 76 := by decide +kernel
  exact strictAtFast_sound (row 14 76) 14 76 hvalid hfast

theorem strict_r14_part77 : ∀ i ∈ List.range 1, StrictCheckAt 14 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 77) 14 77 := by decide +kernel
  exact strictAtFast_sound (row 14 77) 14 77 hvalid hfast

theorem strict_r14_part78 : ∀ i ∈ List.range 1, StrictCheckAt 14 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 78) 14 78 := by decide +kernel
  exact strictAtFast_sound (row 14 78) 14 78 hvalid hfast

theorem strict_r14_part79 : ∀ i ∈ List.range 1, StrictCheckAt 14 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 14 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 14 79) 14 79 := by decide +kernel
  exact strictAtFast_sound (row 14 79) 14 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
