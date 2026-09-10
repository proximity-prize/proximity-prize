import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r17_part16 : ∀ i ∈ List.range 1, StrictCheckAt 17 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 16 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 16) 17 16 := by decide +kernel
  exact strictAtFast_sound (row 17 16) 17 16 hvalid hfast

theorem strict_r17_part17 : ∀ i ∈ List.range 1, StrictCheckAt 17 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 17 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 17) 17 17 := by decide +kernel
  exact strictAtFast_sound (row 17 17) 17 17 hvalid hfast

theorem strict_r17_part18 : ∀ i ∈ List.range 1, StrictCheckAt 17 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 18 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 18) 17 18 := by decide +kernel
  exact strictAtFast_sound (row 17 18) 17 18 hvalid hfast

theorem strict_r17_part19 : ∀ i ∈ List.range 1, StrictCheckAt 17 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 19 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 19) 17 19 := by decide +kernel
  exact strictAtFast_sound (row 17 19) 17 19 hvalid hfast

theorem strict_r17_part20 : ∀ i ∈ List.range 1, StrictCheckAt 17 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 20 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 20) 17 20 := by decide +kernel
  exact strictAtFast_sound (row 17 20) 17 20 hvalid hfast

theorem strict_r17_part21 : ∀ i ∈ List.range 1, StrictCheckAt 17 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 21 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 21) 17 21 := by decide +kernel
  exact strictAtFast_sound (row 17 21) 17 21 hvalid hfast

theorem strict_r17_part22 : ∀ i ∈ List.range 1, StrictCheckAt 17 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 22 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 22) 17 22 := by decide +kernel
  exact strictAtFast_sound (row 17 22) 17 22 hvalid hfast

theorem strict_r17_part23 : ∀ i ∈ List.range 1, StrictCheckAt 17 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 23 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 23) 17 23 := by decide +kernel
  exact strictAtFast_sound (row 17 23) 17 23 hvalid hfast

theorem strict_r17_part24 : ∀ i ∈ List.range 1, StrictCheckAt 17 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 24 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 24) 17 24 := by decide +kernel
  exact strictAtFast_sound (row 17 24) 17 24 hvalid hfast

theorem strict_r17_part25 : ∀ i ∈ List.range 1, StrictCheckAt 17 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 25 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 25) 17 25 := by decide +kernel
  exact strictAtFast_sound (row 17 25) 17 25 hvalid hfast

theorem strict_r17_part26 : ∀ i ∈ List.range 1, StrictCheckAt 17 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 26 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 26) 17 26 := by decide +kernel
  exact strictAtFast_sound (row 17 26) 17 26 hvalid hfast

theorem strict_r17_part27 : ∀ i ∈ List.range 1, StrictCheckAt 17 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 27 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 27) 17 27 := by decide +kernel
  exact strictAtFast_sound (row 17 27) 17 27 hvalid hfast

theorem strict_r17_part28 : ∀ i ∈ List.range 1, StrictCheckAt 17 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 28 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 28) 17 28 := by decide +kernel
  exact strictAtFast_sound (row 17 28) 17 28 hvalid hfast

theorem strict_r17_part29 : ∀ i ∈ List.range 1, StrictCheckAt 17 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 29 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 29) 17 29 := by decide +kernel
  exact strictAtFast_sound (row 17 29) 17 29 hvalid hfast

theorem strict_r17_part30 : ∀ i ∈ List.range 1, StrictCheckAt 17 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 30 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 30) 17 30 := by decide +kernel
  exact strictAtFast_sound (row 17 30) 17 30 hvalid hfast

theorem strict_r17_part31 : ∀ i ∈ List.range 1, StrictCheckAt 17 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 31 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 31) 17 31 := by decide +kernel
  exact strictAtFast_sound (row 17 31) 17 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
