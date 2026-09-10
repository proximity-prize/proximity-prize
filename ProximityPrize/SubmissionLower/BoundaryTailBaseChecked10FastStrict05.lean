import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r10_part64 : ∀ i ∈ List.range 1, StrictCheckAt 10 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 64) 10 64 := by decide +kernel
  exact strictAtFast_sound (row 10 64) 10 64 hvalid hfast

theorem strict_r10_part65 : ∀ i ∈ List.range 1, StrictCheckAt 10 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 65) 10 65 := by decide +kernel
  exact strictAtFast_sound (row 10 65) 10 65 hvalid hfast

theorem strict_r10_part66 : ∀ i ∈ List.range 1, StrictCheckAt 10 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 66) 10 66 := by decide +kernel
  exact strictAtFast_sound (row 10 66) 10 66 hvalid hfast

theorem strict_r10_part67 : ∀ i ∈ List.range 1, StrictCheckAt 10 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 67) 10 67 := by decide +kernel
  exact strictAtFast_sound (row 10 67) 10 67 hvalid hfast

theorem strict_r10_part68 : ∀ i ∈ List.range 1, StrictCheckAt 10 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 68) 10 68 := by decide +kernel
  exact strictAtFast_sound (row 10 68) 10 68 hvalid hfast

theorem strict_r10_part69 : ∀ i ∈ List.range 1, StrictCheckAt 10 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 69) 10 69 := by decide +kernel
  exact strictAtFast_sound (row 10 69) 10 69 hvalid hfast

theorem strict_r10_part70 : ∀ i ∈ List.range 1, StrictCheckAt 10 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 70) 10 70 := by decide +kernel
  exact strictAtFast_sound (row 10 70) 10 70 hvalid hfast

theorem strict_r10_part71 : ∀ i ∈ List.range 1, StrictCheckAt 10 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 71) 10 71 := by decide +kernel
  exact strictAtFast_sound (row 10 71) 10 71 hvalid hfast

theorem strict_r10_part72 : ∀ i ∈ List.range 1, StrictCheckAt 10 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 72) 10 72 := by decide +kernel
  exact strictAtFast_sound (row 10 72) 10 72 hvalid hfast

theorem strict_r10_part73 : ∀ i ∈ List.range 1, StrictCheckAt 10 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 73) 10 73 := by decide +kernel
  exact strictAtFast_sound (row 10 73) 10 73 hvalid hfast

theorem strict_r10_part74 : ∀ i ∈ List.range 1, StrictCheckAt 10 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 74) 10 74 := by decide +kernel
  exact strictAtFast_sound (row 10 74) 10 74 hvalid hfast

theorem strict_r10_part75 : ∀ i ∈ List.range 1, StrictCheckAt 10 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 75) 10 75 := by decide +kernel
  exact strictAtFast_sound (row 10 75) 10 75 hvalid hfast

theorem strict_r10_part76 : ∀ i ∈ List.range 1, StrictCheckAt 10 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 76) 10 76 := by decide +kernel
  exact strictAtFast_sound (row 10 76) 10 76 hvalid hfast

theorem strict_r10_part77 : ∀ i ∈ List.range 1, StrictCheckAt 10 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 77) 10 77 := by decide +kernel
  exact strictAtFast_sound (row 10 77) 10 77 hvalid hfast

theorem strict_r10_part78 : ∀ i ∈ List.range 1, StrictCheckAt 10 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 78) 10 78 := by decide +kernel
  exact strictAtFast_sound (row 10 78) 10 78 hvalid hfast

theorem strict_r10_part79 : ∀ i ∈ List.range 1, StrictCheckAt 10 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 79) 10 79 := by decide +kernel
  exact strictAtFast_sound (row 10 79) 10 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
