import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r27_part64 : ∀ i ∈ List.range 1, StrictCheckAt 27 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 64) 27 64 := by decide +kernel
  exact strictAtFast_sound (row 27 64) 27 64 hvalid hfast

theorem strict_r27_part65 : ∀ i ∈ List.range 1, StrictCheckAt 27 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 65) 27 65 := by decide +kernel
  exact strictAtFast_sound (row 27 65) 27 65 hvalid hfast

theorem strict_r27_part66 : ∀ i ∈ List.range 1, StrictCheckAt 27 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 66) 27 66 := by decide +kernel
  exact strictAtFast_sound (row 27 66) 27 66 hvalid hfast

theorem strict_r27_part67 : ∀ i ∈ List.range 1, StrictCheckAt 27 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 67) 27 67 := by decide +kernel
  exact strictAtFast_sound (row 27 67) 27 67 hvalid hfast

theorem strict_r27_part68 : ∀ i ∈ List.range 1, StrictCheckAt 27 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 68) 27 68 := by decide +kernel
  exact strictAtFast_sound (row 27 68) 27 68 hvalid hfast

theorem strict_r27_part69 : ∀ i ∈ List.range 1, StrictCheckAt 27 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 69) 27 69 := by decide +kernel
  exact strictAtFast_sound (row 27 69) 27 69 hvalid hfast

theorem strict_r27_part70 : ∀ i ∈ List.range 1, StrictCheckAt 27 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 70) 27 70 := by decide +kernel
  exact strictAtFast_sound (row 27 70) 27 70 hvalid hfast

theorem strict_r27_part71 : ∀ i ∈ List.range 1, StrictCheckAt 27 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 71) 27 71 := by decide +kernel
  exact strictAtFast_sound (row 27 71) 27 71 hvalid hfast

theorem strict_r27_part72 : ∀ i ∈ List.range 1, StrictCheckAt 27 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 72) 27 72 := by decide +kernel
  exact strictAtFast_sound (row 27 72) 27 72 hvalid hfast

theorem strict_r27_part73 : ∀ i ∈ List.range 1, StrictCheckAt 27 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 73) 27 73 := by decide +kernel
  exact strictAtFast_sound (row 27 73) 27 73 hvalid hfast

theorem strict_r27_part74 : ∀ i ∈ List.range 1, StrictCheckAt 27 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 74) 27 74 := by decide +kernel
  exact strictAtFast_sound (row 27 74) 27 74 hvalid hfast

theorem strict_r27_part75 : ∀ i ∈ List.range 1, StrictCheckAt 27 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 75) 27 75 := by decide +kernel
  exact strictAtFast_sound (row 27 75) 27 75 hvalid hfast

theorem strict_r27_part76 : ∀ i ∈ List.range 1, StrictCheckAt 27 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 76) 27 76 := by decide +kernel
  exact strictAtFast_sound (row 27 76) 27 76 hvalid hfast

theorem strict_r27_part77 : ∀ i ∈ List.range 1, StrictCheckAt 27 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 77) 27 77 := by decide +kernel
  exact strictAtFast_sound (row 27 77) 27 77 hvalid hfast

theorem strict_r27_part78 : ∀ i ∈ List.range 1, StrictCheckAt 27 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 78) 27 78 := by decide +kernel
  exact strictAtFast_sound (row 27 78) 27 78 hvalid hfast

theorem strict_r27_part79 : ∀ i ∈ List.range 1, StrictCheckAt 27 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 27 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 27 79) 27 79 := by decide +kernel
  exact strictAtFast_sound (row 27 79) 27 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
