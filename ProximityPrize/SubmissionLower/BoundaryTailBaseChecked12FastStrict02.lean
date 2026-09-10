import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r12_part16 : ∀ i ∈ List.range 1, StrictCheckAt 12 (16+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 16 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 16) 12 16 := by decide +kernel
  exact strictAtFast_sound (row 12 16) 12 16 hvalid hfast

theorem strict_r12_part17 : ∀ i ∈ List.range 1, StrictCheckAt 12 (17+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 17 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 17) 12 17 := by decide +kernel
  exact strictAtFast_sound (row 12 17) 12 17 hvalid hfast

theorem strict_r12_part18 : ∀ i ∈ List.range 1, StrictCheckAt 12 (18+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 18 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 18) 12 18 := by decide +kernel
  exact strictAtFast_sound (row 12 18) 12 18 hvalid hfast

theorem strict_r12_part19 : ∀ i ∈ List.range 1, StrictCheckAt 12 (19+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 19 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 19) 12 19 := by decide +kernel
  exact strictAtFast_sound (row 12 19) 12 19 hvalid hfast

theorem strict_r12_part20 : ∀ i ∈ List.range 1, StrictCheckAt 12 (20+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 20 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 20) 12 20 := by decide +kernel
  exact strictAtFast_sound (row 12 20) 12 20 hvalid hfast

theorem strict_r12_part21 : ∀ i ∈ List.range 1, StrictCheckAt 12 (21+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 21 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 21) 12 21 := by decide +kernel
  exact strictAtFast_sound (row 12 21) 12 21 hvalid hfast

theorem strict_r12_part22 : ∀ i ∈ List.range 1, StrictCheckAt 12 (22+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 22 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 22) 12 22 := by decide +kernel
  exact strictAtFast_sound (row 12 22) 12 22 hvalid hfast

theorem strict_r12_part23 : ∀ i ∈ List.range 1, StrictCheckAt 12 (23+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 23 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 23) 12 23 := by decide +kernel
  exact strictAtFast_sound (row 12 23) 12 23 hvalid hfast

theorem strict_r12_part24 : ∀ i ∈ List.range 1, StrictCheckAt 12 (24+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 24 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 24) 12 24 := by decide +kernel
  exact strictAtFast_sound (row 12 24) 12 24 hvalid hfast

theorem strict_r12_part25 : ∀ i ∈ List.range 1, StrictCheckAt 12 (25+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 25 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 25) 12 25 := by decide +kernel
  exact strictAtFast_sound (row 12 25) 12 25 hvalid hfast

theorem strict_r12_part26 : ∀ i ∈ List.range 1, StrictCheckAt 12 (26+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 26 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 26) 12 26 := by decide +kernel
  exact strictAtFast_sound (row 12 26) 12 26 hvalid hfast

theorem strict_r12_part27 : ∀ i ∈ List.range 1, StrictCheckAt 12 (27+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 27 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 27) 12 27 := by decide +kernel
  exact strictAtFast_sound (row 12 27) 12 27 hvalid hfast

theorem strict_r12_part28 : ∀ i ∈ List.range 1, StrictCheckAt 12 (28+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 28 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 28) 12 28 := by decide +kernel
  exact strictAtFast_sound (row 12 28) 12 28 hvalid hfast

theorem strict_r12_part29 : ∀ i ∈ List.range 1, StrictCheckAt 12 (29+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 29 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 29) 12 29 := by decide +kernel
  exact strictAtFast_sound (row 12 29) 12 29 hvalid hfast

theorem strict_r12_part30 : ∀ i ∈ List.range 1, StrictCheckAt 12 (30+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 30 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 30) 12 30 := by decide +kernel
  exact strictAtFast_sound (row 12 30) 12 30 hvalid hfast

theorem strict_r12_part31 : ∀ i ∈ List.range 1, StrictCheckAt 12 (31+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 12 31 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 12 31) 12 31 := by decide +kernel
  exact strictAtFast_sound (row 12 31) 12 31 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
