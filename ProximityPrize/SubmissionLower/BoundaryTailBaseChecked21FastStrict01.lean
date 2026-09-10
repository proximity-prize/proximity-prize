import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r21_part0 : ∀ i ∈ List.range 1, StrictCheckAt 21 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 0) 21 0 := by decide +kernel
  exact strictAtFast_sound (row 21 0) 21 0 hvalid hfast

theorem strict_r21_part1 : ∀ i ∈ List.range 1, StrictCheckAt 21 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 1) 21 1 := by decide +kernel
  exact strictAtFast_sound (row 21 1) 21 1 hvalid hfast

theorem strict_r21_part2 : ∀ i ∈ List.range 1, StrictCheckAt 21 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 2) 21 2 := by decide +kernel
  exact strictAtFast_sound (row 21 2) 21 2 hvalid hfast

theorem strict_r21_part3 : ∀ i ∈ List.range 1, StrictCheckAt 21 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 3) 21 3 := by decide +kernel
  exact strictAtFast_sound (row 21 3) 21 3 hvalid hfast

theorem strict_r21_part4 : ∀ i ∈ List.range 1, StrictCheckAt 21 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 4) 21 4 := by decide +kernel
  exact strictAtFast_sound (row 21 4) 21 4 hvalid hfast

theorem strict_r21_part5 : ∀ i ∈ List.range 1, StrictCheckAt 21 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 5) 21 5 := by decide +kernel
  exact strictAtFast_sound (row 21 5) 21 5 hvalid hfast

theorem strict_r21_part6 : ∀ i ∈ List.range 1, StrictCheckAt 21 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 6) 21 6 := by decide +kernel
  exact strictAtFast_sound (row 21 6) 21 6 hvalid hfast

theorem strict_r21_part7 : ∀ i ∈ List.range 1, StrictCheckAt 21 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 7) 21 7 := by decide +kernel
  exact strictAtFast_sound (row 21 7) 21 7 hvalid hfast

theorem strict_r21_part8 : ∀ i ∈ List.range 1, StrictCheckAt 21 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 8) 21 8 := by decide +kernel
  exact strictAtFast_sound (row 21 8) 21 8 hvalid hfast

theorem strict_r21_part9 : ∀ i ∈ List.range 1, StrictCheckAt 21 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 9) 21 9 := by decide +kernel
  exact strictAtFast_sound (row 21 9) 21 9 hvalid hfast

theorem strict_r21_part10 : ∀ i ∈ List.range 1, StrictCheckAt 21 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 10) 21 10 := by decide +kernel
  exact strictAtFast_sound (row 21 10) 21 10 hvalid hfast

theorem strict_r21_part11 : ∀ i ∈ List.range 1, StrictCheckAt 21 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 11) 21 11 := by decide +kernel
  exact strictAtFast_sound (row 21 11) 21 11 hvalid hfast

theorem strict_r21_part12 : ∀ i ∈ List.range 1, StrictCheckAt 21 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 12) 21 12 := by decide +kernel
  exact strictAtFast_sound (row 21 12) 21 12 hvalid hfast

theorem strict_r21_part13 : ∀ i ∈ List.range 1, StrictCheckAt 21 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 13) 21 13 := by decide +kernel
  exact strictAtFast_sound (row 21 13) 21 13 hvalid hfast

theorem strict_r21_part14 : ∀ i ∈ List.range 1, StrictCheckAt 21 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 14) 21 14 := by decide +kernel
  exact strictAtFast_sound (row 21 14) 21 14 hvalid hfast

theorem strict_r21_part15 : ∀ i ∈ List.range 1, StrictCheckAt 21 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 15) 21 15 := by decide +kernel
  exact strictAtFast_sound (row 21 15) 21 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
