import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastZero08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r12_part0 : ∀ i ∈ List.range 1, StrictCheckAt 12 (0+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 0 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 0) 12 0 := by decide +kernel
  exact strictAtFast_sound (row 12 0) 12 0 hvalid hfast

theorem strict_r12_part1 : ∀ i ∈ List.range 1, StrictCheckAt 12 (1+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 1 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 1) 12 1 := by decide +kernel
  exact strictAtFast_sound (row 12 1) 12 1 hvalid hfast

theorem strict_r12_part2 : ∀ i ∈ List.range 1, StrictCheckAt 12 (2+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 2 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 2) 12 2 := by decide +kernel
  exact strictAtFast_sound (row 12 2) 12 2 hvalid hfast

theorem strict_r12_part3 : ∀ i ∈ List.range 1, StrictCheckAt 12 (3+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 3 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 3) 12 3 := by decide +kernel
  exact strictAtFast_sound (row 12 3) 12 3 hvalid hfast

theorem strict_r12_part4 : ∀ i ∈ List.range 1, StrictCheckAt 12 (4+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 4 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 4) 12 4 := by decide +kernel
  exact strictAtFast_sound (row 12 4) 12 4 hvalid hfast

theorem strict_r12_part5 : ∀ i ∈ List.range 1, StrictCheckAt 12 (5+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 5 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 5) 12 5 := by decide +kernel
  exact strictAtFast_sound (row 12 5) 12 5 hvalid hfast

theorem strict_r12_part6 : ∀ i ∈ List.range 1, StrictCheckAt 12 (6+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 6 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 6) 12 6 := by decide +kernel
  exact strictAtFast_sound (row 12 6) 12 6 hvalid hfast

theorem strict_r12_part7 : ∀ i ∈ List.range 1, StrictCheckAt 12 (7+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 7 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 7) 12 7 := by decide +kernel
  exact strictAtFast_sound (row 12 7) 12 7 hvalid hfast

theorem strict_r12_part8 : ∀ i ∈ List.range 1, StrictCheckAt 12 (8+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 8 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 8) 12 8 := by decide +kernel
  exact strictAtFast_sound (row 12 8) 12 8 hvalid hfast

theorem strict_r12_part9 : ∀ i ∈ List.range 1, StrictCheckAt 12 (9+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 9 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 9) 12 9 := by decide +kernel
  exact strictAtFast_sound (row 12 9) 12 9 hvalid hfast

theorem strict_r12_part10 : ∀ i ∈ List.range 1, StrictCheckAt 12 (10+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 10 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 10) 12 10 := by decide +kernel
  exact strictAtFast_sound (row 12 10) 12 10 hvalid hfast

theorem strict_r12_part11 : ∀ i ∈ List.range 1, StrictCheckAt 12 (11+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 11 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 11) 12 11 := by decide +kernel
  exact strictAtFast_sound (row 12 11) 12 11 hvalid hfast

theorem strict_r12_part12 : ∀ i ∈ List.range 1, StrictCheckAt 12 (12+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 12 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 12) 12 12 := by decide +kernel
  exact strictAtFast_sound (row 12 12) 12 12 hvalid hfast

theorem strict_r12_part13 : ∀ i ∈ List.range 1, StrictCheckAt 12 (13+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 13 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 13) 12 13 := by decide +kernel
  exact strictAtFast_sound (row 12 13) 12 13 hvalid hfast

theorem strict_r12_part14 : ∀ i ∈ List.range 1, StrictCheckAt 12 (14+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 14 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 14) 12 14 := by decide +kernel
  exact strictAtFast_sound (row 12 14) 12 14 hvalid hfast

theorem strict_r12_part15 : ∀ i ∈ List.range 1, StrictCheckAt 12 (15+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 15 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 15) 12 15 := by decide +kernel
  exact strictAtFast_sound (row 12 15) 12 15 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
