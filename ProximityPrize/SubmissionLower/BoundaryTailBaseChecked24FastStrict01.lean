import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r24_part0 : ∀ i ∈ List.range 1, StrictCheckAt 24 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 0) 24 0 := by decide +kernel
  exact strictAtFast_sound (row 24 0) 24 0 hvalid hfast

theorem strict_r24_part1 : ∀ i ∈ List.range 1, StrictCheckAt 24 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 1) 24 1 := by decide +kernel
  exact strictAtFast_sound (row 24 1) 24 1 hvalid hfast

theorem strict_r24_part2 : ∀ i ∈ List.range 1, StrictCheckAt 24 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 2) 24 2 := by decide +kernel
  exact strictAtFast_sound (row 24 2) 24 2 hvalid hfast

theorem strict_r24_part3 : ∀ i ∈ List.range 1, StrictCheckAt 24 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 3) 24 3 := by decide +kernel
  exact strictAtFast_sound (row 24 3) 24 3 hvalid hfast

theorem strict_r24_part4 : ∀ i ∈ List.range 1, StrictCheckAt 24 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 4) 24 4 := by decide +kernel
  exact strictAtFast_sound (row 24 4) 24 4 hvalid hfast

theorem strict_r24_part5 : ∀ i ∈ List.range 1, StrictCheckAt 24 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 5) 24 5 := by decide +kernel
  exact strictAtFast_sound (row 24 5) 24 5 hvalid hfast

theorem strict_r24_part6 : ∀ i ∈ List.range 1, StrictCheckAt 24 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 6) 24 6 := by decide +kernel
  exact strictAtFast_sound (row 24 6) 24 6 hvalid hfast

theorem strict_r24_part7 : ∀ i ∈ List.range 1, StrictCheckAt 24 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 7) 24 7 := by decide +kernel
  exact strictAtFast_sound (row 24 7) 24 7 hvalid hfast

theorem strict_r24_part8 : ∀ i ∈ List.range 1, StrictCheckAt 24 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 8) 24 8 := by decide +kernel
  exact strictAtFast_sound (row 24 8) 24 8 hvalid hfast

theorem strict_r24_part9 : ∀ i ∈ List.range 1, StrictCheckAt 24 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 9) 24 9 := by decide +kernel
  exact strictAtFast_sound (row 24 9) 24 9 hvalid hfast

theorem strict_r24_part10 : ∀ i ∈ List.range 1, StrictCheckAt 24 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 10) 24 10 := by decide +kernel
  exact strictAtFast_sound (row 24 10) 24 10 hvalid hfast

theorem strict_r24_part11 : ∀ i ∈ List.range 1, StrictCheckAt 24 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 11) 24 11 := by decide +kernel
  exact strictAtFast_sound (row 24 11) 24 11 hvalid hfast

theorem strict_r24_part12 : ∀ i ∈ List.range 1, StrictCheckAt 24 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 12) 24 12 := by decide +kernel
  exact strictAtFast_sound (row 24 12) 24 12 hvalid hfast

theorem strict_r24_part13 : ∀ i ∈ List.range 1, StrictCheckAt 24 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 13) 24 13 := by decide +kernel
  exact strictAtFast_sound (row 24 13) 24 13 hvalid hfast

theorem strict_r24_part14 : ∀ i ∈ List.range 1, StrictCheckAt 24 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 14) 24 14 := by decide +kernel
  exact strictAtFast_sound (row 24 14) 24 14 hvalid hfast

theorem strict_r24_part15 : ∀ i ∈ List.range 1, StrictCheckAt 24 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 24 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 24 15) 24 15 := by decide +kernel
  exact strictAtFast_sound (row 24 15) 24 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
