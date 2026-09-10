import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r22_part64 : ∀ i ∈ List.range 1, StrictCheckAt 22 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 64) 22 64 := by decide +kernel
  exact strictAtFast_sound (row 22 64) 22 64 hvalid hfast

theorem strict_r22_part65 : ∀ i ∈ List.range 1, StrictCheckAt 22 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 65) 22 65 := by decide +kernel
  exact strictAtFast_sound (row 22 65) 22 65 hvalid hfast

theorem strict_r22_part66 : ∀ i ∈ List.range 1, StrictCheckAt 22 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 66) 22 66 := by decide +kernel
  exact strictAtFast_sound (row 22 66) 22 66 hvalid hfast

theorem strict_r22_part67 : ∀ i ∈ List.range 1, StrictCheckAt 22 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 67) 22 67 := by decide +kernel
  exact strictAtFast_sound (row 22 67) 22 67 hvalid hfast

theorem strict_r22_part68 : ∀ i ∈ List.range 1, StrictCheckAt 22 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 68) 22 68 := by decide +kernel
  exact strictAtFast_sound (row 22 68) 22 68 hvalid hfast

theorem strict_r22_part69 : ∀ i ∈ List.range 1, StrictCheckAt 22 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 69) 22 69 := by decide +kernel
  exact strictAtFast_sound (row 22 69) 22 69 hvalid hfast

theorem strict_r22_part70 : ∀ i ∈ List.range 1, StrictCheckAt 22 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 70) 22 70 := by decide +kernel
  exact strictAtFast_sound (row 22 70) 22 70 hvalid hfast

theorem strict_r22_part71 : ∀ i ∈ List.range 1, StrictCheckAt 22 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 71) 22 71 := by decide +kernel
  exact strictAtFast_sound (row 22 71) 22 71 hvalid hfast

theorem strict_r22_part72 : ∀ i ∈ List.range 1, StrictCheckAt 22 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 72) 22 72 := by decide +kernel
  exact strictAtFast_sound (row 22 72) 22 72 hvalid hfast

theorem strict_r22_part73 : ∀ i ∈ List.range 1, StrictCheckAt 22 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 73) 22 73 := by decide +kernel
  exact strictAtFast_sound (row 22 73) 22 73 hvalid hfast

theorem strict_r22_part74 : ∀ i ∈ List.range 1, StrictCheckAt 22 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 74) 22 74 := by decide +kernel
  exact strictAtFast_sound (row 22 74) 22 74 hvalid hfast

theorem strict_r22_part75 : ∀ i ∈ List.range 1, StrictCheckAt 22 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 75) 22 75 := by decide +kernel
  exact strictAtFast_sound (row 22 75) 22 75 hvalid hfast

theorem strict_r22_part76 : ∀ i ∈ List.range 1, StrictCheckAt 22 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 76) 22 76 := by decide +kernel
  exact strictAtFast_sound (row 22 76) 22 76 hvalid hfast

theorem strict_r22_part77 : ∀ i ∈ List.range 1, StrictCheckAt 22 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 77) 22 77 := by decide +kernel
  exact strictAtFast_sound (row 22 77) 22 77 hvalid hfast

theorem strict_r22_part78 : ∀ i ∈ List.range 1, StrictCheckAt 22 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 78) 22 78 := by decide +kernel
  exact strictAtFast_sound (row 22 78) 22 78 hvalid hfast

theorem strict_r22_part79 : ∀ i ∈ List.range 1, StrictCheckAt 22 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 79) 22 79 := by decide +kernel
  exact strictAtFast_sound (row 22 79) 22 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
