import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r19_part64 : ∀ i ∈ List.range 1, StrictCheckAt 19 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 64) 19 64 := by decide +kernel
  exact strictAtFast_sound (row 19 64) 19 64 hvalid hfast

theorem strict_r19_part65 : ∀ i ∈ List.range 1, StrictCheckAt 19 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 65) 19 65 := by decide +kernel
  exact strictAtFast_sound (row 19 65) 19 65 hvalid hfast

theorem strict_r19_part66 : ∀ i ∈ List.range 1, StrictCheckAt 19 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 66) 19 66 := by decide +kernel
  exact strictAtFast_sound (row 19 66) 19 66 hvalid hfast

theorem strict_r19_part67 : ∀ i ∈ List.range 1, StrictCheckAt 19 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 67) 19 67 := by decide +kernel
  exact strictAtFast_sound (row 19 67) 19 67 hvalid hfast

theorem strict_r19_part68 : ∀ i ∈ List.range 1, StrictCheckAt 19 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 68) 19 68 := by decide +kernel
  exact strictAtFast_sound (row 19 68) 19 68 hvalid hfast

theorem strict_r19_part69 : ∀ i ∈ List.range 1, StrictCheckAt 19 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 69) 19 69 := by decide +kernel
  exact strictAtFast_sound (row 19 69) 19 69 hvalid hfast

theorem strict_r19_part70 : ∀ i ∈ List.range 1, StrictCheckAt 19 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 70) 19 70 := by decide +kernel
  exact strictAtFast_sound (row 19 70) 19 70 hvalid hfast

theorem strict_r19_part71 : ∀ i ∈ List.range 1, StrictCheckAt 19 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 71) 19 71 := by decide +kernel
  exact strictAtFast_sound (row 19 71) 19 71 hvalid hfast

theorem strict_r19_part72 : ∀ i ∈ List.range 1, StrictCheckAt 19 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 72) 19 72 := by decide +kernel
  exact strictAtFast_sound (row 19 72) 19 72 hvalid hfast

theorem strict_r19_part73 : ∀ i ∈ List.range 1, StrictCheckAt 19 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 73) 19 73 := by decide +kernel
  exact strictAtFast_sound (row 19 73) 19 73 hvalid hfast

theorem strict_r19_part74 : ∀ i ∈ List.range 1, StrictCheckAt 19 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 74) 19 74 := by decide +kernel
  exact strictAtFast_sound (row 19 74) 19 74 hvalid hfast

theorem strict_r19_part75 : ∀ i ∈ List.range 1, StrictCheckAt 19 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 75) 19 75 := by decide +kernel
  exact strictAtFast_sound (row 19 75) 19 75 hvalid hfast

theorem strict_r19_part76 : ∀ i ∈ List.range 1, StrictCheckAt 19 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 76) 19 76 := by decide +kernel
  exact strictAtFast_sound (row 19 76) 19 76 hvalid hfast

theorem strict_r19_part77 : ∀ i ∈ List.range 1, StrictCheckAt 19 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 77) 19 77 := by decide +kernel
  exact strictAtFast_sound (row 19 77) 19 77 hvalid hfast

theorem strict_r19_part78 : ∀ i ∈ List.range 1, StrictCheckAt 19 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 78) 19 78 := by decide +kernel
  exact strictAtFast_sound (row 19 78) 19 78 hvalid hfast

theorem strict_r19_part79 : ∀ i ∈ List.range 1, StrictCheckAt 19 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 79) 19 79 := by decide +kernel
  exact strictAtFast_sound (row 19 79) 19 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
