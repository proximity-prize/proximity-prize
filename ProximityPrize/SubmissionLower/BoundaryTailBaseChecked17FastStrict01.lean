import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastCorrect01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r17_part0 : ∀ i ∈ List.range 1, StrictCheckAt 17 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 0) 17 0 := by decide +kernel
  exact strictAtFast_sound (row 17 0) 17 0 hvalid hfast

theorem strict_r17_part1 : ∀ i ∈ List.range 1, StrictCheckAt 17 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 1) 17 1 := by decide +kernel
  exact strictAtFast_sound (row 17 1) 17 1 hvalid hfast

theorem strict_r17_part2 : ∀ i ∈ List.range 1, StrictCheckAt 17 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 2) 17 2 := by decide +kernel
  exact strictAtFast_sound (row 17 2) 17 2 hvalid hfast

theorem strict_r17_part3 : ∀ i ∈ List.range 1, StrictCheckAt 17 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 3) 17 3 := by decide +kernel
  exact strictAtFast_sound (row 17 3) 17 3 hvalid hfast

theorem strict_r17_part4 : ∀ i ∈ List.range 1, StrictCheckAt 17 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 4) 17 4 := by decide +kernel
  exact strictAtFast_sound (row 17 4) 17 4 hvalid hfast

theorem strict_r17_part5 : ∀ i ∈ List.range 1, StrictCheckAt 17 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 5) 17 5 := by decide +kernel
  exact strictAtFast_sound (row 17 5) 17 5 hvalid hfast

theorem strict_r17_part6 : ∀ i ∈ List.range 1, StrictCheckAt 17 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 6) 17 6 := by decide +kernel
  exact strictAtFast_sound (row 17 6) 17 6 hvalid hfast

theorem strict_r17_part7 : ∀ i ∈ List.range 1, StrictCheckAt 17 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 7) 17 7 := by decide +kernel
  exact strictAtFast_sound (row 17 7) 17 7 hvalid hfast

theorem strict_r17_part8 : ∀ i ∈ List.range 1, StrictCheckAt 17 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 8) 17 8 := by decide +kernel
  exact strictAtFast_sound (row 17 8) 17 8 hvalid hfast

theorem strict_r17_part9 : ∀ i ∈ List.range 1, StrictCheckAt 17 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 9) 17 9 := by decide +kernel
  exact strictAtFast_sound (row 17 9) 17 9 hvalid hfast

theorem strict_r17_part10 : ∀ i ∈ List.range 1, StrictCheckAt 17 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 10) 17 10 := by decide +kernel
  exact strictAtFast_sound (row 17 10) 17 10 hvalid hfast

theorem strict_r17_part11 : ∀ i ∈ List.range 1, StrictCheckAt 17 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 11) 17 11 := by decide +kernel
  exact strictAtFast_sound (row 17 11) 17 11 hvalid hfast

theorem strict_r17_part12 : ∀ i ∈ List.range 1, StrictCheckAt 17 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 12) 17 12 := by decide +kernel
  exact strictAtFast_sound (row 17 12) 17 12 hvalid hfast

theorem strict_r17_part13 : ∀ i ∈ List.range 1, StrictCheckAt 17 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 13) 17 13 := by decide +kernel
  exact strictAtFast_sound (row 17 13) 17 13 hvalid hfast

theorem strict_r17_part14 : ∀ i ∈ List.range 1, StrictCheckAt 17 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 14) 17 14 := by decide +kernel
  exact strictAtFast_sound (row 17 14) 17 14 hvalid hfast

theorem strict_r17_part15 : ∀ i ∈ List.range 1, StrictCheckAt 17 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 15) 17 15 := by decide +kernel
  exact strictAtFast_sound (row 17 15) 17 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
