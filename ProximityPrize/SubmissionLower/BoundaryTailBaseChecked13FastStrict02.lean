import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r13_part16 : ∀ i ∈ List.range 1, StrictCheckAt 13 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 16 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 16) 13 16 := by decide +kernel
  exact strictAtFast_sound (row 13 16) 13 16 hvalid hfast

theorem strict_r13_part17 : ∀ i ∈ List.range 1, StrictCheckAt 13 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 17 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 17) 13 17 := by decide +kernel
  exact strictAtFast_sound (row 13 17) 13 17 hvalid hfast

theorem strict_r13_part18 : ∀ i ∈ List.range 1, StrictCheckAt 13 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 18 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 18) 13 18 := by decide +kernel
  exact strictAtFast_sound (row 13 18) 13 18 hvalid hfast

theorem strict_r13_part19 : ∀ i ∈ List.range 1, StrictCheckAt 13 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 19 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 19) 13 19 := by decide +kernel
  exact strictAtFast_sound (row 13 19) 13 19 hvalid hfast

theorem strict_r13_part20 : ∀ i ∈ List.range 1, StrictCheckAt 13 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 20 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 20) 13 20 := by decide +kernel
  exact strictAtFast_sound (row 13 20) 13 20 hvalid hfast

theorem strict_r13_part21 : ∀ i ∈ List.range 1, StrictCheckAt 13 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 21 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 21) 13 21 := by decide +kernel
  exact strictAtFast_sound (row 13 21) 13 21 hvalid hfast

theorem strict_r13_part22 : ∀ i ∈ List.range 1, StrictCheckAt 13 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 22 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 22) 13 22 := by decide +kernel
  exact strictAtFast_sound (row 13 22) 13 22 hvalid hfast

theorem strict_r13_part23 : ∀ i ∈ List.range 1, StrictCheckAt 13 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 23 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 23) 13 23 := by decide +kernel
  exact strictAtFast_sound (row 13 23) 13 23 hvalid hfast

theorem strict_r13_part24 : ∀ i ∈ List.range 1, StrictCheckAt 13 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 24 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 24) 13 24 := by decide +kernel
  exact strictAtFast_sound (row 13 24) 13 24 hvalid hfast

theorem strict_r13_part25 : ∀ i ∈ List.range 1, StrictCheckAt 13 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 25 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 25) 13 25 := by decide +kernel
  exact strictAtFast_sound (row 13 25) 13 25 hvalid hfast

theorem strict_r13_part26 : ∀ i ∈ List.range 1, StrictCheckAt 13 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 26 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 26) 13 26 := by decide +kernel
  exact strictAtFast_sound (row 13 26) 13 26 hvalid hfast

theorem strict_r13_part27 : ∀ i ∈ List.range 1, StrictCheckAt 13 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 27 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 27) 13 27 := by decide +kernel
  exact strictAtFast_sound (row 13 27) 13 27 hvalid hfast

theorem strict_r13_part28 : ∀ i ∈ List.range 1, StrictCheckAt 13 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 28 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 28) 13 28 := by decide +kernel
  exact strictAtFast_sound (row 13 28) 13 28 hvalid hfast

theorem strict_r13_part29 : ∀ i ∈ List.range 1, StrictCheckAt 13 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 29 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 29) 13 29 := by decide +kernel
  exact strictAtFast_sound (row 13 29) 13 29 hvalid hfast

theorem strict_r13_part30 : ∀ i ∈ List.range 1, StrictCheckAt 13 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 30 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 30) 13 30 := by decide +kernel
  exact strictAtFast_sound (row 13 30) 13 30 hvalid hfast

theorem strict_r13_part31 : ∀ i ∈ List.range 1, StrictCheckAt 13 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 31 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 31) 13 31 := by decide +kernel
  exact strictAtFast_sound (row 13 31) 13 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
