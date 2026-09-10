import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r22_part0 : ∀ i ∈ List.range 1, StrictCheckAt 22 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 0) 22 0 := by decide +kernel
  exact strictAtFast_sound (row 22 0) 22 0 hvalid hfast

theorem strict_r22_part1 : ∀ i ∈ List.range 1, StrictCheckAt 22 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 1) 22 1 := by decide +kernel
  exact strictAtFast_sound (row 22 1) 22 1 hvalid hfast

theorem strict_r22_part2 : ∀ i ∈ List.range 1, StrictCheckAt 22 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 2) 22 2 := by decide +kernel
  exact strictAtFast_sound (row 22 2) 22 2 hvalid hfast

theorem strict_r22_part3 : ∀ i ∈ List.range 1, StrictCheckAt 22 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 3) 22 3 := by decide +kernel
  exact strictAtFast_sound (row 22 3) 22 3 hvalid hfast

theorem strict_r22_part4 : ∀ i ∈ List.range 1, StrictCheckAt 22 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 4) 22 4 := by decide +kernel
  exact strictAtFast_sound (row 22 4) 22 4 hvalid hfast

theorem strict_r22_part5 : ∀ i ∈ List.range 1, StrictCheckAt 22 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 5) 22 5 := by decide +kernel
  exact strictAtFast_sound (row 22 5) 22 5 hvalid hfast

theorem strict_r22_part6 : ∀ i ∈ List.range 1, StrictCheckAt 22 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 6) 22 6 := by decide +kernel
  exact strictAtFast_sound (row 22 6) 22 6 hvalid hfast

theorem strict_r22_part7 : ∀ i ∈ List.range 1, StrictCheckAt 22 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 7) 22 7 := by decide +kernel
  exact strictAtFast_sound (row 22 7) 22 7 hvalid hfast

theorem strict_r22_part8 : ∀ i ∈ List.range 1, StrictCheckAt 22 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 8) 22 8 := by decide +kernel
  exact strictAtFast_sound (row 22 8) 22 8 hvalid hfast

theorem strict_r22_part9 : ∀ i ∈ List.range 1, StrictCheckAt 22 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 9) 22 9 := by decide +kernel
  exact strictAtFast_sound (row 22 9) 22 9 hvalid hfast

theorem strict_r22_part10 : ∀ i ∈ List.range 1, StrictCheckAt 22 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 10) 22 10 := by decide +kernel
  exact strictAtFast_sound (row 22 10) 22 10 hvalid hfast

theorem strict_r22_part11 : ∀ i ∈ List.range 1, StrictCheckAt 22 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 11) 22 11 := by decide +kernel
  exact strictAtFast_sound (row 22 11) 22 11 hvalid hfast

theorem strict_r22_part12 : ∀ i ∈ List.range 1, StrictCheckAt 22 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 12) 22 12 := by decide +kernel
  exact strictAtFast_sound (row 22 12) 22 12 hvalid hfast

theorem strict_r22_part13 : ∀ i ∈ List.range 1, StrictCheckAt 22 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 13) 22 13 := by decide +kernel
  exact strictAtFast_sound (row 22 13) 22 13 hvalid hfast

theorem strict_r22_part14 : ∀ i ∈ List.range 1, StrictCheckAt 22 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 14) 22 14 := by decide +kernel
  exact strictAtFast_sound (row 22 14) 22 14 hvalid hfast

theorem strict_r22_part15 : ∀ i ∈ List.range 1, StrictCheckAt 22 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 15) 22 15 := by decide +kernel
  exact strictAtFast_sound (row 22 15) 22 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
