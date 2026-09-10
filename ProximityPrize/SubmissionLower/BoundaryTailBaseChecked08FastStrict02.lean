import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r8_part16 : ∀ i ∈ List.range 1, StrictCheckAt 8 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 16 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 16) 8 16 := by decide +kernel
  exact strictAtFast_sound (row 8 16) 8 16 hvalid hfast

theorem strict_r8_part17 : ∀ i ∈ List.range 1, StrictCheckAt 8 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 17 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 17) 8 17 := by decide +kernel
  exact strictAtFast_sound (row 8 17) 8 17 hvalid hfast

theorem strict_r8_part18 : ∀ i ∈ List.range 1, StrictCheckAt 8 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 18 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 18) 8 18 := by decide +kernel
  exact strictAtFast_sound (row 8 18) 8 18 hvalid hfast

theorem strict_r8_part19 : ∀ i ∈ List.range 1, StrictCheckAt 8 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 19 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 19) 8 19 := by decide +kernel
  exact strictAtFast_sound (row 8 19) 8 19 hvalid hfast

theorem strict_r8_part20 : ∀ i ∈ List.range 1, StrictCheckAt 8 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 20 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 20) 8 20 := by decide +kernel
  exact strictAtFast_sound (row 8 20) 8 20 hvalid hfast

theorem strict_r8_part21 : ∀ i ∈ List.range 1, StrictCheckAt 8 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 21 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 21) 8 21 := by decide +kernel
  exact strictAtFast_sound (row 8 21) 8 21 hvalid hfast

theorem strict_r8_part22 : ∀ i ∈ List.range 1, StrictCheckAt 8 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 22 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 22) 8 22 := by decide +kernel
  exact strictAtFast_sound (row 8 22) 8 22 hvalid hfast

theorem strict_r8_part23 : ∀ i ∈ List.range 1, StrictCheckAt 8 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 23 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 23) 8 23 := by decide +kernel
  exact strictAtFast_sound (row 8 23) 8 23 hvalid hfast

theorem strict_r8_part24 : ∀ i ∈ List.range 1, StrictCheckAt 8 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 24 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 24) 8 24 := by decide +kernel
  exact strictAtFast_sound (row 8 24) 8 24 hvalid hfast

theorem strict_r8_part25 : ∀ i ∈ List.range 1, StrictCheckAt 8 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 25 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 25) 8 25 := by decide +kernel
  exact strictAtFast_sound (row 8 25) 8 25 hvalid hfast

theorem strict_r8_part26 : ∀ i ∈ List.range 1, StrictCheckAt 8 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 26 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 26) 8 26 := by decide +kernel
  exact strictAtFast_sound (row 8 26) 8 26 hvalid hfast

theorem strict_r8_part27 : ∀ i ∈ List.range 1, StrictCheckAt 8 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 27 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 27) 8 27 := by decide +kernel
  exact strictAtFast_sound (row 8 27) 8 27 hvalid hfast

theorem strict_r8_part28 : ∀ i ∈ List.range 1, StrictCheckAt 8 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 28 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 28) 8 28 := by decide +kernel
  exact strictAtFast_sound (row 8 28) 8 28 hvalid hfast

theorem strict_r8_part29 : ∀ i ∈ List.range 1, StrictCheckAt 8 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 29 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 29) 8 29 := by decide +kernel
  exact strictAtFast_sound (row 8 29) 8 29 hvalid hfast

theorem strict_r8_part30 : ∀ i ∈ List.range 1, StrictCheckAt 8 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 30 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 30) 8 30 := by decide +kernel
  exact strictAtFast_sound (row 8 30) 8 30 hvalid hfast

theorem strict_r8_part31 : ∀ i ∈ List.range 1, StrictCheckAt 8 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 8 31 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 8 31) 8 31 := by decide +kernel
  exact strictAtFast_sound (row 8 31) 8 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
