import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r26_part64 : ∀ i ∈ List.range 1, StrictCheckAt 26 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 64) 26 64 := by decide +kernel
  exact strictAtFast_sound (row 26 64) 26 64 hvalid hfast

theorem strict_r26_part65 : ∀ i ∈ List.range 1, StrictCheckAt 26 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 65) 26 65 := by decide +kernel
  exact strictAtFast_sound (row 26 65) 26 65 hvalid hfast

theorem strict_r26_part66 : ∀ i ∈ List.range 1, StrictCheckAt 26 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 66) 26 66 := by decide +kernel
  exact strictAtFast_sound (row 26 66) 26 66 hvalid hfast

theorem strict_r26_part67 : ∀ i ∈ List.range 1, StrictCheckAt 26 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 67) 26 67 := by decide +kernel
  exact strictAtFast_sound (row 26 67) 26 67 hvalid hfast

theorem strict_r26_part68 : ∀ i ∈ List.range 1, StrictCheckAt 26 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 68) 26 68 := by decide +kernel
  exact strictAtFast_sound (row 26 68) 26 68 hvalid hfast

theorem strict_r26_part69 : ∀ i ∈ List.range 1, StrictCheckAt 26 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 69) 26 69 := by decide +kernel
  exact strictAtFast_sound (row 26 69) 26 69 hvalid hfast

theorem strict_r26_part70 : ∀ i ∈ List.range 1, StrictCheckAt 26 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 70) 26 70 := by decide +kernel
  exact strictAtFast_sound (row 26 70) 26 70 hvalid hfast

theorem strict_r26_part71 : ∀ i ∈ List.range 1, StrictCheckAt 26 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 71) 26 71 := by decide +kernel
  exact strictAtFast_sound (row 26 71) 26 71 hvalid hfast

theorem strict_r26_part72 : ∀ i ∈ List.range 1, StrictCheckAt 26 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 72) 26 72 := by decide +kernel
  exact strictAtFast_sound (row 26 72) 26 72 hvalid hfast

theorem strict_r26_part73 : ∀ i ∈ List.range 1, StrictCheckAt 26 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 73) 26 73 := by decide +kernel
  exact strictAtFast_sound (row 26 73) 26 73 hvalid hfast

theorem strict_r26_part74 : ∀ i ∈ List.range 1, StrictCheckAt 26 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 74) 26 74 := by decide +kernel
  exact strictAtFast_sound (row 26 74) 26 74 hvalid hfast

theorem strict_r26_part75 : ∀ i ∈ List.range 1, StrictCheckAt 26 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 75) 26 75 := by decide +kernel
  exact strictAtFast_sound (row 26 75) 26 75 hvalid hfast

theorem strict_r26_part76 : ∀ i ∈ List.range 1, StrictCheckAt 26 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 76) 26 76 := by decide +kernel
  exact strictAtFast_sound (row 26 76) 26 76 hvalid hfast

theorem strict_r26_part77 : ∀ i ∈ List.range 1, StrictCheckAt 26 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 77) 26 77 := by decide +kernel
  exact strictAtFast_sound (row 26 77) 26 77 hvalid hfast

theorem strict_r26_part78 : ∀ i ∈ List.range 1, StrictCheckAt 26 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 78) 26 78 := by decide +kernel
  exact strictAtFast_sound (row 26 78) 26 78 hvalid hfast

theorem strict_r26_part79 : ∀ i ∈ List.range 1, StrictCheckAt 26 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 26 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 26 79) 26 79 := by decide +kernel
  exact strictAtFast_sound (row 26 79) 26 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
