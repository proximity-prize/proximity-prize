import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r25_part16 : ∀ i ∈ List.range 1, StrictCheckAt 25 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 16 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 16) 25 16 := by decide +kernel
  exact strictAtFast_sound (row 25 16) 25 16 hvalid hfast

theorem strict_r25_part17 : ∀ i ∈ List.range 1, StrictCheckAt 25 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 17 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 17) 25 17 := by decide +kernel
  exact strictAtFast_sound (row 25 17) 25 17 hvalid hfast

theorem strict_r25_part18 : ∀ i ∈ List.range 1, StrictCheckAt 25 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 18 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 18) 25 18 := by decide +kernel
  exact strictAtFast_sound (row 25 18) 25 18 hvalid hfast

theorem strict_r25_part19 : ∀ i ∈ List.range 1, StrictCheckAt 25 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 19 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 19) 25 19 := by decide +kernel
  exact strictAtFast_sound (row 25 19) 25 19 hvalid hfast

theorem strict_r25_part20 : ∀ i ∈ List.range 1, StrictCheckAt 25 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 20 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 20) 25 20 := by decide +kernel
  exact strictAtFast_sound (row 25 20) 25 20 hvalid hfast

theorem strict_r25_part21 : ∀ i ∈ List.range 1, StrictCheckAt 25 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 21 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 21) 25 21 := by decide +kernel
  exact strictAtFast_sound (row 25 21) 25 21 hvalid hfast

theorem strict_r25_part22 : ∀ i ∈ List.range 1, StrictCheckAt 25 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 22 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 22) 25 22 := by decide +kernel
  exact strictAtFast_sound (row 25 22) 25 22 hvalid hfast

theorem strict_r25_part23 : ∀ i ∈ List.range 1, StrictCheckAt 25 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 23 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 23) 25 23 := by decide +kernel
  exact strictAtFast_sound (row 25 23) 25 23 hvalid hfast

theorem strict_r25_part24 : ∀ i ∈ List.range 1, StrictCheckAt 25 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 24 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 24) 25 24 := by decide +kernel
  exact strictAtFast_sound (row 25 24) 25 24 hvalid hfast

theorem strict_r25_part25 : ∀ i ∈ List.range 1, StrictCheckAt 25 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 25 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 25) 25 25 := by decide +kernel
  exact strictAtFast_sound (row 25 25) 25 25 hvalid hfast

theorem strict_r25_part26 : ∀ i ∈ List.range 1, StrictCheckAt 25 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 26 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 26) 25 26 := by decide +kernel
  exact strictAtFast_sound (row 25 26) 25 26 hvalid hfast

theorem strict_r25_part27 : ∀ i ∈ List.range 1, StrictCheckAt 25 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 27 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 27) 25 27 := by decide +kernel
  exact strictAtFast_sound (row 25 27) 25 27 hvalid hfast

theorem strict_r25_part28 : ∀ i ∈ List.range 1, StrictCheckAt 25 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 28 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 28) 25 28 := by decide +kernel
  exact strictAtFast_sound (row 25 28) 25 28 hvalid hfast

theorem strict_r25_part29 : ∀ i ∈ List.range 1, StrictCheckAt 25 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 29 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 29) 25 29 := by decide +kernel
  exact strictAtFast_sound (row 25 29) 25 29 hvalid hfast

theorem strict_r25_part30 : ∀ i ∈ List.range 1, StrictCheckAt 25 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 30 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 30) 25 30 := by decide +kernel
  exact strictAtFast_sound (row 25 30) 25 30 hvalid hfast

theorem strict_r25_part31 : ∀ i ∈ List.range 1, StrictCheckAt 25 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 31 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 31) 25 31 := by decide +kernel
  exact strictAtFast_sound (row 25 31) 25 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
