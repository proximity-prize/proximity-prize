import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r13_part48 : ∀ i ∈ List.range 1, StrictCheckAt 13 (48+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 48 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 48) 13 48 := by decide +kernel
  exact strictAtFast_sound (row 13 48) 13 48 hvalid hfast

theorem strict_r13_part49 : ∀ i ∈ List.range 1, StrictCheckAt 13 (49+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 49 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 49) 13 49 := by decide +kernel
  exact strictAtFast_sound (row 13 49) 13 49 hvalid hfast

theorem strict_r13_part50 : ∀ i ∈ List.range 1, StrictCheckAt 13 (50+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 50 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 50) 13 50 := by decide +kernel
  exact strictAtFast_sound (row 13 50) 13 50 hvalid hfast

theorem strict_r13_part51 : ∀ i ∈ List.range 1, StrictCheckAt 13 (51+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 51 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 51) 13 51 := by decide +kernel
  exact strictAtFast_sound (row 13 51) 13 51 hvalid hfast

theorem strict_r13_part52 : ∀ i ∈ List.range 1, StrictCheckAt 13 (52+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 52 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 52) 13 52 := by decide +kernel
  exact strictAtFast_sound (row 13 52) 13 52 hvalid hfast

theorem strict_r13_part53 : ∀ i ∈ List.range 1, StrictCheckAt 13 (53+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 53 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 53) 13 53 := by decide +kernel
  exact strictAtFast_sound (row 13 53) 13 53 hvalid hfast

theorem strict_r13_part54 : ∀ i ∈ List.range 1, StrictCheckAt 13 (54+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 54 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 54) 13 54 := by decide +kernel
  exact strictAtFast_sound (row 13 54) 13 54 hvalid hfast

theorem strict_r13_part55 : ∀ i ∈ List.range 1, StrictCheckAt 13 (55+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 55 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 55) 13 55 := by decide +kernel
  exact strictAtFast_sound (row 13 55) 13 55 hvalid hfast

theorem strict_r13_part56 : ∀ i ∈ List.range 1, StrictCheckAt 13 (56+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 56 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 56) 13 56 := by decide +kernel
  exact strictAtFast_sound (row 13 56) 13 56 hvalid hfast

theorem strict_r13_part57 : ∀ i ∈ List.range 1, StrictCheckAt 13 (57+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 57 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 57) 13 57 := by decide +kernel
  exact strictAtFast_sound (row 13 57) 13 57 hvalid hfast

theorem strict_r13_part58 : ∀ i ∈ List.range 1, StrictCheckAt 13 (58+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 58 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 58) 13 58 := by decide +kernel
  exact strictAtFast_sound (row 13 58) 13 58 hvalid hfast

theorem strict_r13_part59 : ∀ i ∈ List.range 1, StrictCheckAt 13 (59+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 59 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 59) 13 59 := by decide +kernel
  exact strictAtFast_sound (row 13 59) 13 59 hvalid hfast

theorem strict_r13_part60 : ∀ i ∈ List.range 1, StrictCheckAt 13 (60+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 60 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 60) 13 60 := by decide +kernel
  exact strictAtFast_sound (row 13 60) 13 60 hvalid hfast

theorem strict_r13_part61 : ∀ i ∈ List.range 1, StrictCheckAt 13 (61+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 61 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 61) 13 61 := by decide +kernel
  exact strictAtFast_sound (row 13 61) 13 61 hvalid hfast

theorem strict_r13_part62 : ∀ i ∈ List.range 1, StrictCheckAt 13 (62+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 62 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 62) 13 62 := by decide +kernel
  exact strictAtFast_sound (row 13 62) 13 62 hvalid hfast

theorem strict_r13_part63 : ∀ i ∈ List.range 1, StrictCheckAt 13 (63+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 13 63 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 13 63) 13 63 := by decide +kernel
  exact strictAtFast_sound (row 13 63) 13 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
