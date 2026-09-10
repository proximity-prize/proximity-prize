import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r20_part64 : ∀ i ∈ List.range 1, StrictCheckAt 20 (64+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 64 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 64) 20 64 := by decide +kernel
  exact strictAtFast_sound (row 20 64) 20 64 hvalid hfast

theorem strict_r20_part65 : ∀ i ∈ List.range 1, StrictCheckAt 20 (65+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 65 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 65) 20 65 := by decide +kernel
  exact strictAtFast_sound (row 20 65) 20 65 hvalid hfast

theorem strict_r20_part66 : ∀ i ∈ List.range 1, StrictCheckAt 20 (66+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 66 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 66) 20 66 := by decide +kernel
  exact strictAtFast_sound (row 20 66) 20 66 hvalid hfast

theorem strict_r20_part67 : ∀ i ∈ List.range 1, StrictCheckAt 20 (67+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 67 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 67) 20 67 := by decide +kernel
  exact strictAtFast_sound (row 20 67) 20 67 hvalid hfast

theorem strict_r20_part68 : ∀ i ∈ List.range 1, StrictCheckAt 20 (68+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 68 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 68) 20 68 := by decide +kernel
  exact strictAtFast_sound (row 20 68) 20 68 hvalid hfast

theorem strict_r20_part69 : ∀ i ∈ List.range 1, StrictCheckAt 20 (69+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 69 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 69) 20 69 := by decide +kernel
  exact strictAtFast_sound (row 20 69) 20 69 hvalid hfast

theorem strict_r20_part70 : ∀ i ∈ List.range 1, StrictCheckAt 20 (70+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 70 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 70) 20 70 := by decide +kernel
  exact strictAtFast_sound (row 20 70) 20 70 hvalid hfast

theorem strict_r20_part71 : ∀ i ∈ List.range 1, StrictCheckAt 20 (71+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 71 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 71) 20 71 := by decide +kernel
  exact strictAtFast_sound (row 20 71) 20 71 hvalid hfast

theorem strict_r20_part72 : ∀ i ∈ List.range 1, StrictCheckAt 20 (72+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 72 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 72) 20 72 := by decide +kernel
  exact strictAtFast_sound (row 20 72) 20 72 hvalid hfast

theorem strict_r20_part73 : ∀ i ∈ List.range 1, StrictCheckAt 20 (73+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 73 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 73) 20 73 := by decide +kernel
  exact strictAtFast_sound (row 20 73) 20 73 hvalid hfast

theorem strict_r20_part74 : ∀ i ∈ List.range 1, StrictCheckAt 20 (74+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 74 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 74) 20 74 := by decide +kernel
  exact strictAtFast_sound (row 20 74) 20 74 hvalid hfast

theorem strict_r20_part75 : ∀ i ∈ List.range 1, StrictCheckAt 20 (75+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 75 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 75) 20 75 := by decide +kernel
  exact strictAtFast_sound (row 20 75) 20 75 hvalid hfast

theorem strict_r20_part76 : ∀ i ∈ List.range 1, StrictCheckAt 20 (76+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 76 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 76) 20 76 := by decide +kernel
  exact strictAtFast_sound (row 20 76) 20 76 hvalid hfast

theorem strict_r20_part77 : ∀ i ∈ List.range 1, StrictCheckAt 20 (77+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 77 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 77) 20 77 := by decide +kernel
  exact strictAtFast_sound (row 20 77) 20 77 hvalid hfast

theorem strict_r20_part78 : ∀ i ∈ List.range 1, StrictCheckAt 20 (78+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 78 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 78) 20 78 := by decide +kernel
  exact strictAtFast_sound (row 20 78) 20 78 hvalid hfast

theorem strict_r20_part79 : ∀ i ∈ List.range 1, StrictCheckAt 20 (79+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 79 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 79) 20 79 := by decide +kernel
  exact strictAtFast_sound (row 20 79) 20 79 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
