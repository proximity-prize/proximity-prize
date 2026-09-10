import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r19_part0 : ∀ i ∈ List.range 1, StrictCheckAt 19 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 0) 19 0 := by decide +kernel
  exact strictAtFast_sound (row 19 0) 19 0 hvalid hfast

theorem strict_r19_part1 : ∀ i ∈ List.range 1, StrictCheckAt 19 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 1) 19 1 := by decide +kernel
  exact strictAtFast_sound (row 19 1) 19 1 hvalid hfast

theorem strict_r19_part2 : ∀ i ∈ List.range 1, StrictCheckAt 19 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 2) 19 2 := by decide +kernel
  exact strictAtFast_sound (row 19 2) 19 2 hvalid hfast

theorem strict_r19_part3 : ∀ i ∈ List.range 1, StrictCheckAt 19 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 3) 19 3 := by decide +kernel
  exact strictAtFast_sound (row 19 3) 19 3 hvalid hfast

theorem strict_r19_part4 : ∀ i ∈ List.range 1, StrictCheckAt 19 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 4) 19 4 := by decide +kernel
  exact strictAtFast_sound (row 19 4) 19 4 hvalid hfast

theorem strict_r19_part5 : ∀ i ∈ List.range 1, StrictCheckAt 19 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 5) 19 5 := by decide +kernel
  exact strictAtFast_sound (row 19 5) 19 5 hvalid hfast

theorem strict_r19_part6 : ∀ i ∈ List.range 1, StrictCheckAt 19 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 6) 19 6 := by decide +kernel
  exact strictAtFast_sound (row 19 6) 19 6 hvalid hfast

theorem strict_r19_part7 : ∀ i ∈ List.range 1, StrictCheckAt 19 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 7) 19 7 := by decide +kernel
  exact strictAtFast_sound (row 19 7) 19 7 hvalid hfast

theorem strict_r19_part8 : ∀ i ∈ List.range 1, StrictCheckAt 19 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 8) 19 8 := by decide +kernel
  exact strictAtFast_sound (row 19 8) 19 8 hvalid hfast

theorem strict_r19_part9 : ∀ i ∈ List.range 1, StrictCheckAt 19 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 9) 19 9 := by decide +kernel
  exact strictAtFast_sound (row 19 9) 19 9 hvalid hfast

theorem strict_r19_part10 : ∀ i ∈ List.range 1, StrictCheckAt 19 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 10) 19 10 := by decide +kernel
  exact strictAtFast_sound (row 19 10) 19 10 hvalid hfast

theorem strict_r19_part11 : ∀ i ∈ List.range 1, StrictCheckAt 19 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 11) 19 11 := by decide +kernel
  exact strictAtFast_sound (row 19 11) 19 11 hvalid hfast

theorem strict_r19_part12 : ∀ i ∈ List.range 1, StrictCheckAt 19 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 12) 19 12 := by decide +kernel
  exact strictAtFast_sound (row 19 12) 19 12 hvalid hfast

theorem strict_r19_part13 : ∀ i ∈ List.range 1, StrictCheckAt 19 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 13) 19 13 := by decide +kernel
  exact strictAtFast_sound (row 19 13) 19 13 hvalid hfast

theorem strict_r19_part14 : ∀ i ∈ List.range 1, StrictCheckAt 19 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 14) 19 14 := by decide +kernel
  exact strictAtFast_sound (row 19 14) 19 14 hvalid hfast

theorem strict_r19_part15 : ∀ i ∈ List.range 1, StrictCheckAt 19 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 15) 19 15 := by decide +kernel
  exact strictAtFast_sound (row 19 15) 19 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
