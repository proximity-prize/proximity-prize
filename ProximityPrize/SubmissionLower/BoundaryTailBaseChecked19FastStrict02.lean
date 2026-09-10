import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r19_part16 : ∀ i ∈ List.range 1, StrictCheckAt 19 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 16 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 16) 19 16 := by decide +kernel
  exact strictAtFast_sound (row 19 16) 19 16 hvalid hfast

theorem strict_r19_part17 : ∀ i ∈ List.range 1, StrictCheckAt 19 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 17 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 17) 19 17 := by decide +kernel
  exact strictAtFast_sound (row 19 17) 19 17 hvalid hfast

theorem strict_r19_part18 : ∀ i ∈ List.range 1, StrictCheckAt 19 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 18 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 18) 19 18 := by decide +kernel
  exact strictAtFast_sound (row 19 18) 19 18 hvalid hfast

theorem strict_r19_part19 : ∀ i ∈ List.range 1, StrictCheckAt 19 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 19 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 19) 19 19 := by decide +kernel
  exact strictAtFast_sound (row 19 19) 19 19 hvalid hfast

theorem strict_r19_part20 : ∀ i ∈ List.range 1, StrictCheckAt 19 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 20 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 20) 19 20 := by decide +kernel
  exact strictAtFast_sound (row 19 20) 19 20 hvalid hfast

theorem strict_r19_part21 : ∀ i ∈ List.range 1, StrictCheckAt 19 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 21 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 21) 19 21 := by decide +kernel
  exact strictAtFast_sound (row 19 21) 19 21 hvalid hfast

theorem strict_r19_part22 : ∀ i ∈ List.range 1, StrictCheckAt 19 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 22 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 22) 19 22 := by decide +kernel
  exact strictAtFast_sound (row 19 22) 19 22 hvalid hfast

theorem strict_r19_part23 : ∀ i ∈ List.range 1, StrictCheckAt 19 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 23 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 23) 19 23 := by decide +kernel
  exact strictAtFast_sound (row 19 23) 19 23 hvalid hfast

theorem strict_r19_part24 : ∀ i ∈ List.range 1, StrictCheckAt 19 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 24 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 24) 19 24 := by decide +kernel
  exact strictAtFast_sound (row 19 24) 19 24 hvalid hfast

theorem strict_r19_part25 : ∀ i ∈ List.range 1, StrictCheckAt 19 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 25 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 25) 19 25 := by decide +kernel
  exact strictAtFast_sound (row 19 25) 19 25 hvalid hfast

theorem strict_r19_part26 : ∀ i ∈ List.range 1, StrictCheckAt 19 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 26 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 26) 19 26 := by decide +kernel
  exact strictAtFast_sound (row 19 26) 19 26 hvalid hfast

theorem strict_r19_part27 : ∀ i ∈ List.range 1, StrictCheckAt 19 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 27 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 27) 19 27 := by decide +kernel
  exact strictAtFast_sound (row 19 27) 19 27 hvalid hfast

theorem strict_r19_part28 : ∀ i ∈ List.range 1, StrictCheckAt 19 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 28 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 28) 19 28 := by decide +kernel
  exact strictAtFast_sound (row 19 28) 19 28 hvalid hfast

theorem strict_r19_part29 : ∀ i ∈ List.range 1, StrictCheckAt 19 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 29 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 29) 19 29 := by decide +kernel
  exact strictAtFast_sound (row 19 29) 19 29 hvalid hfast

theorem strict_r19_part30 : ∀ i ∈ List.range 1, StrictCheckAt 19 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 30 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 30) 19 30 := by decide +kernel
  exact strictAtFast_sound (row 19 30) 19 30 hvalid hfast

theorem strict_r19_part31 : ∀ i ∈ List.range 1, StrictCheckAt 19 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 19 31 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 19 31) 19 31 := by decide +kernel
  exact strictAtFast_sound (row 19 31) 19 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
