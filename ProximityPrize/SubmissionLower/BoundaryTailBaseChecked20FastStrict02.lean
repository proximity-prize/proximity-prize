import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r20_part16 : ∀ i ∈ List.range 1, StrictCheckAt 20 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 16 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 16) 20 16 := by decide +kernel
  exact strictAtFast_sound (row 20 16) 20 16 hvalid hfast

theorem strict_r20_part17 : ∀ i ∈ List.range 1, StrictCheckAt 20 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 17 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 17) 20 17 := by decide +kernel
  exact strictAtFast_sound (row 20 17) 20 17 hvalid hfast

theorem strict_r20_part18 : ∀ i ∈ List.range 1, StrictCheckAt 20 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 18 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 18) 20 18 := by decide +kernel
  exact strictAtFast_sound (row 20 18) 20 18 hvalid hfast

theorem strict_r20_part19 : ∀ i ∈ List.range 1, StrictCheckAt 20 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 19 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 19) 20 19 := by decide +kernel
  exact strictAtFast_sound (row 20 19) 20 19 hvalid hfast

theorem strict_r20_part20 : ∀ i ∈ List.range 1, StrictCheckAt 20 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 20 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 20) 20 20 := by decide +kernel
  exact strictAtFast_sound (row 20 20) 20 20 hvalid hfast

theorem strict_r20_part21 : ∀ i ∈ List.range 1, StrictCheckAt 20 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 21 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 21) 20 21 := by decide +kernel
  exact strictAtFast_sound (row 20 21) 20 21 hvalid hfast

theorem strict_r20_part22 : ∀ i ∈ List.range 1, StrictCheckAt 20 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 22 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 22) 20 22 := by decide +kernel
  exact strictAtFast_sound (row 20 22) 20 22 hvalid hfast

theorem strict_r20_part23 : ∀ i ∈ List.range 1, StrictCheckAt 20 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 23 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 23) 20 23 := by decide +kernel
  exact strictAtFast_sound (row 20 23) 20 23 hvalid hfast

theorem strict_r20_part24 : ∀ i ∈ List.range 1, StrictCheckAt 20 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 24 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 24) 20 24 := by decide +kernel
  exact strictAtFast_sound (row 20 24) 20 24 hvalid hfast

theorem strict_r20_part25 : ∀ i ∈ List.range 1, StrictCheckAt 20 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 25 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 25) 20 25 := by decide +kernel
  exact strictAtFast_sound (row 20 25) 20 25 hvalid hfast

theorem strict_r20_part26 : ∀ i ∈ List.range 1, StrictCheckAt 20 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 26 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 26) 20 26 := by decide +kernel
  exact strictAtFast_sound (row 20 26) 20 26 hvalid hfast

theorem strict_r20_part27 : ∀ i ∈ List.range 1, StrictCheckAt 20 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 27 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 27) 20 27 := by decide +kernel
  exact strictAtFast_sound (row 20 27) 20 27 hvalid hfast

theorem strict_r20_part28 : ∀ i ∈ List.range 1, StrictCheckAt 20 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 28 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 28) 20 28 := by decide +kernel
  exact strictAtFast_sound (row 20 28) 20 28 hvalid hfast

theorem strict_r20_part29 : ∀ i ∈ List.range 1, StrictCheckAt 20 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 29 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 29) 20 29 := by decide +kernel
  exact strictAtFast_sound (row 20 29) 20 29 hvalid hfast

theorem strict_r20_part30 : ∀ i ∈ List.range 1, StrictCheckAt 20 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 30 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 30) 20 30 := by decide +kernel
  exact strictAtFast_sound (row 20 30) 20 30 hvalid hfast

theorem strict_r20_part31 : ∀ i ∈ List.range 1, StrictCheckAt 20 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 31 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 31) 20 31 := by decide +kernel
  exact strictAtFast_sound (row 20 31) 20 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
