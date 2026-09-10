import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastZero09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r10_part0 : ∀ i ∈ List.range 1, StrictCheckAt 10 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 0) 10 0 := by decide +kernel
  exact strictAtFast_sound (row 10 0) 10 0 hvalid hfast

theorem strict_r10_part1 : ∀ i ∈ List.range 1, StrictCheckAt 10 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 1) 10 1 := by decide +kernel
  exact strictAtFast_sound (row 10 1) 10 1 hvalid hfast

theorem strict_r10_part2 : ∀ i ∈ List.range 1, StrictCheckAt 10 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 2) 10 2 := by decide +kernel
  exact strictAtFast_sound (row 10 2) 10 2 hvalid hfast

theorem strict_r10_part3 : ∀ i ∈ List.range 1, StrictCheckAt 10 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 3) 10 3 := by decide +kernel
  exact strictAtFast_sound (row 10 3) 10 3 hvalid hfast

theorem strict_r10_part4 : ∀ i ∈ List.range 1, StrictCheckAt 10 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 4) 10 4 := by decide +kernel
  exact strictAtFast_sound (row 10 4) 10 4 hvalid hfast

theorem strict_r10_part5 : ∀ i ∈ List.range 1, StrictCheckAt 10 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 5) 10 5 := by decide +kernel
  exact strictAtFast_sound (row 10 5) 10 5 hvalid hfast

theorem strict_r10_part6 : ∀ i ∈ List.range 1, StrictCheckAt 10 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 6) 10 6 := by decide +kernel
  exact strictAtFast_sound (row 10 6) 10 6 hvalid hfast

theorem strict_r10_part7 : ∀ i ∈ List.range 1, StrictCheckAt 10 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 7) 10 7 := by decide +kernel
  exact strictAtFast_sound (row 10 7) 10 7 hvalid hfast

theorem strict_r10_part8 : ∀ i ∈ List.range 1, StrictCheckAt 10 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 8) 10 8 := by decide +kernel
  exact strictAtFast_sound (row 10 8) 10 8 hvalid hfast

theorem strict_r10_part9 : ∀ i ∈ List.range 1, StrictCheckAt 10 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 9) 10 9 := by decide +kernel
  exact strictAtFast_sound (row 10 9) 10 9 hvalid hfast

theorem strict_r10_part10 : ∀ i ∈ List.range 1, StrictCheckAt 10 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 10) 10 10 := by decide +kernel
  exact strictAtFast_sound (row 10 10) 10 10 hvalid hfast

theorem strict_r10_part11 : ∀ i ∈ List.range 1, StrictCheckAt 10 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 11) 10 11 := by decide +kernel
  exact strictAtFast_sound (row 10 11) 10 11 hvalid hfast

theorem strict_r10_part12 : ∀ i ∈ List.range 1, StrictCheckAt 10 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 12) 10 12 := by decide +kernel
  exact strictAtFast_sound (row 10 12) 10 12 hvalid hfast

theorem strict_r10_part13 : ∀ i ∈ List.range 1, StrictCheckAt 10 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 13) 10 13 := by decide +kernel
  exact strictAtFast_sound (row 10 13) 10 13 hvalid hfast

theorem strict_r10_part14 : ∀ i ∈ List.range 1, StrictCheckAt 10 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 14) 10 14 := by decide +kernel
  exact strictAtFast_sound (row 10 14) 10 14 hvalid hfast

theorem strict_r10_part15 : ∀ i ∈ List.range 1, StrictCheckAt 10 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 10 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 10 15) 10 15 := by decide +kernel
  exact strictAtFast_sound (row 10 15) 10 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
