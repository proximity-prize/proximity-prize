import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r17_part64 : ∀ i ∈ List.range 1, StrictCheckAt 17 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 64) 17 64 := by decide +kernel
  exact strictAtFast_sound (row 17 64) 17 64 hvalid hfast

theorem strict_r17_part65 : ∀ i ∈ List.range 1, StrictCheckAt 17 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 65) 17 65 := by decide +kernel
  exact strictAtFast_sound (row 17 65) 17 65 hvalid hfast

theorem strict_r17_part66 : ∀ i ∈ List.range 1, StrictCheckAt 17 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 66) 17 66 := by decide +kernel
  exact strictAtFast_sound (row 17 66) 17 66 hvalid hfast

theorem strict_r17_part67 : ∀ i ∈ List.range 1, StrictCheckAt 17 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 67) 17 67 := by decide +kernel
  exact strictAtFast_sound (row 17 67) 17 67 hvalid hfast

theorem strict_r17_part68 : ∀ i ∈ List.range 1, StrictCheckAt 17 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 68) 17 68 := by decide +kernel
  exact strictAtFast_sound (row 17 68) 17 68 hvalid hfast

theorem strict_r17_part69 : ∀ i ∈ List.range 1, StrictCheckAt 17 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 69) 17 69 := by decide +kernel
  exact strictAtFast_sound (row 17 69) 17 69 hvalid hfast

theorem strict_r17_part70 : ∀ i ∈ List.range 1, StrictCheckAt 17 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 70) 17 70 := by decide +kernel
  exact strictAtFast_sound (row 17 70) 17 70 hvalid hfast

theorem strict_r17_part71 : ∀ i ∈ List.range 1, StrictCheckAt 17 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 71) 17 71 := by decide +kernel
  exact strictAtFast_sound (row 17 71) 17 71 hvalid hfast

theorem strict_r17_part72 : ∀ i ∈ List.range 1, StrictCheckAt 17 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 72) 17 72 := by decide +kernel
  exact strictAtFast_sound (row 17 72) 17 72 hvalid hfast

theorem strict_r17_part73 : ∀ i ∈ List.range 1, StrictCheckAt 17 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 73) 17 73 := by decide +kernel
  exact strictAtFast_sound (row 17 73) 17 73 hvalid hfast

theorem strict_r17_part74 : ∀ i ∈ List.range 1, StrictCheckAt 17 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 74) 17 74 := by decide +kernel
  exact strictAtFast_sound (row 17 74) 17 74 hvalid hfast

theorem strict_r17_part75 : ∀ i ∈ List.range 1, StrictCheckAt 17 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 75) 17 75 := by decide +kernel
  exact strictAtFast_sound (row 17 75) 17 75 hvalid hfast

theorem strict_r17_part76 : ∀ i ∈ List.range 1, StrictCheckAt 17 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 76) 17 76 := by decide +kernel
  exact strictAtFast_sound (row 17 76) 17 76 hvalid hfast

theorem strict_r17_part77 : ∀ i ∈ List.range 1, StrictCheckAt 17 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 77) 17 77 := by decide +kernel
  exact strictAtFast_sound (row 17 77) 17 77 hvalid hfast

theorem strict_r17_part78 : ∀ i ∈ List.range 1, StrictCheckAt 17 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 78) 17 78 := by decide +kernel
  exact strictAtFast_sound (row 17 78) 17 78 hvalid hfast

theorem strict_r17_part79 : ∀ i ∈ List.range 1, StrictCheckAt 17 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 79) 17 79 := by decide +kernel
  exact strictAtFast_sound (row 17 79) 17 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
