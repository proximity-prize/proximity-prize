import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r12_part64 : ∀ i ∈ List.range 1, StrictCheckAt 12 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 64) 12 64 := by decide +kernel
  exact strictAtFast_sound (row 12 64) 12 64 hvalid hfast

theorem strict_r12_part65 : ∀ i ∈ List.range 1, StrictCheckAt 12 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 65) 12 65 := by decide +kernel
  exact strictAtFast_sound (row 12 65) 12 65 hvalid hfast

theorem strict_r12_part66 : ∀ i ∈ List.range 1, StrictCheckAt 12 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 66) 12 66 := by decide +kernel
  exact strictAtFast_sound (row 12 66) 12 66 hvalid hfast

theorem strict_r12_part67 : ∀ i ∈ List.range 1, StrictCheckAt 12 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 67) 12 67 := by decide +kernel
  exact strictAtFast_sound (row 12 67) 12 67 hvalid hfast

theorem strict_r12_part68 : ∀ i ∈ List.range 1, StrictCheckAt 12 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 68) 12 68 := by decide +kernel
  exact strictAtFast_sound (row 12 68) 12 68 hvalid hfast

theorem strict_r12_part69 : ∀ i ∈ List.range 1, StrictCheckAt 12 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 69) 12 69 := by decide +kernel
  exact strictAtFast_sound (row 12 69) 12 69 hvalid hfast

theorem strict_r12_part70 : ∀ i ∈ List.range 1, StrictCheckAt 12 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 70) 12 70 := by decide +kernel
  exact strictAtFast_sound (row 12 70) 12 70 hvalid hfast

theorem strict_r12_part71 : ∀ i ∈ List.range 1, StrictCheckAt 12 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 71) 12 71 := by decide +kernel
  exact strictAtFast_sound (row 12 71) 12 71 hvalid hfast

theorem strict_r12_part72 : ∀ i ∈ List.range 1, StrictCheckAt 12 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 72) 12 72 := by decide +kernel
  exact strictAtFast_sound (row 12 72) 12 72 hvalid hfast

theorem strict_r12_part73 : ∀ i ∈ List.range 1, StrictCheckAt 12 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 73) 12 73 := by decide +kernel
  exact strictAtFast_sound (row 12 73) 12 73 hvalid hfast

theorem strict_r12_part74 : ∀ i ∈ List.range 1, StrictCheckAt 12 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 74) 12 74 := by decide +kernel
  exact strictAtFast_sound (row 12 74) 12 74 hvalid hfast

theorem strict_r12_part75 : ∀ i ∈ List.range 1, StrictCheckAt 12 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 75) 12 75 := by decide +kernel
  exact strictAtFast_sound (row 12 75) 12 75 hvalid hfast

theorem strict_r12_part76 : ∀ i ∈ List.range 1, StrictCheckAt 12 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 76) 12 76 := by decide +kernel
  exact strictAtFast_sound (row 12 76) 12 76 hvalid hfast

theorem strict_r12_part77 : ∀ i ∈ List.range 1, StrictCheckAt 12 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 77) 12 77 := by decide +kernel
  exact strictAtFast_sound (row 12 77) 12 77 hvalid hfast

theorem strict_r12_part78 : ∀ i ∈ List.range 1, StrictCheckAt 12 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 78) 12 78 := by decide +kernel
  exact strictAtFast_sound (row 12 78) 12 78 hvalid hfast

theorem strict_r12_part79 : ∀ i ∈ List.range 1, StrictCheckAt 12 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 79) 12 79 := by decide +kernel
  exact strictAtFast_sound (row 12 79) 12 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
