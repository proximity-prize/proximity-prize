import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r15_part0 : ∀ i ∈ List.range 1, StrictCheckAt 15 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 0) 15 0 := by decide +kernel
  exact strictAtFast_sound (row 15 0) 15 0 hvalid hfast

theorem strict_r15_part1 : ∀ i ∈ List.range 1, StrictCheckAt 15 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 1) 15 1 := by decide +kernel
  exact strictAtFast_sound (row 15 1) 15 1 hvalid hfast

theorem strict_r15_part2 : ∀ i ∈ List.range 1, StrictCheckAt 15 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 2) 15 2 := by decide +kernel
  exact strictAtFast_sound (row 15 2) 15 2 hvalid hfast

theorem strict_r15_part3 : ∀ i ∈ List.range 1, StrictCheckAt 15 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 3) 15 3 := by decide +kernel
  exact strictAtFast_sound (row 15 3) 15 3 hvalid hfast

theorem strict_r15_part4 : ∀ i ∈ List.range 1, StrictCheckAt 15 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 4) 15 4 := by decide +kernel
  exact strictAtFast_sound (row 15 4) 15 4 hvalid hfast

theorem strict_r15_part5 : ∀ i ∈ List.range 1, StrictCheckAt 15 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 5) 15 5 := by decide +kernel
  exact strictAtFast_sound (row 15 5) 15 5 hvalid hfast

theorem strict_r15_part6 : ∀ i ∈ List.range 1, StrictCheckAt 15 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 6) 15 6 := by decide +kernel
  exact strictAtFast_sound (row 15 6) 15 6 hvalid hfast

theorem strict_r15_part7 : ∀ i ∈ List.range 1, StrictCheckAt 15 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 7) 15 7 := by decide +kernel
  exact strictAtFast_sound (row 15 7) 15 7 hvalid hfast

theorem strict_r15_part8 : ∀ i ∈ List.range 1, StrictCheckAt 15 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 8) 15 8 := by decide +kernel
  exact strictAtFast_sound (row 15 8) 15 8 hvalid hfast

theorem strict_r15_part9 : ∀ i ∈ List.range 1, StrictCheckAt 15 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 9) 15 9 := by decide +kernel
  exact strictAtFast_sound (row 15 9) 15 9 hvalid hfast

theorem strict_r15_part10 : ∀ i ∈ List.range 1, StrictCheckAt 15 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 10) 15 10 := by decide +kernel
  exact strictAtFast_sound (row 15 10) 15 10 hvalid hfast

theorem strict_r15_part11 : ∀ i ∈ List.range 1, StrictCheckAt 15 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 11) 15 11 := by decide +kernel
  exact strictAtFast_sound (row 15 11) 15 11 hvalid hfast

theorem strict_r15_part12 : ∀ i ∈ List.range 1, StrictCheckAt 15 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 12) 15 12 := by decide +kernel
  exact strictAtFast_sound (row 15 12) 15 12 hvalid hfast

theorem strict_r15_part13 : ∀ i ∈ List.range 1, StrictCheckAt 15 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 13) 15 13 := by decide +kernel
  exact strictAtFast_sound (row 15 13) 15 13 hvalid hfast

theorem strict_r15_part14 : ∀ i ∈ List.range 1, StrictCheckAt 15 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 14) 15 14 := by decide +kernel
  exact strictAtFast_sound (row 15 14) 15 14 hvalid hfast

theorem strict_r15_part15 : ∀ i ∈ List.range 1, StrictCheckAt 15 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 15) 15 15 := by decide +kernel
  exact strictAtFast_sound (row 15 15) 15 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
