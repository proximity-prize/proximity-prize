import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r21_part48 : ∀ i ∈ List.range 1, StrictCheckAt 21 (48+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 48 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 48) 21 48 := by decide +kernel
  exact strictAtFast_sound (row 21 48) 21 48 hvalid hfast

theorem strict_r21_part49 : ∀ i ∈ List.range 1, StrictCheckAt 21 (49+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 49 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 49) 21 49 := by decide +kernel
  exact strictAtFast_sound (row 21 49) 21 49 hvalid hfast

theorem strict_r21_part50 : ∀ i ∈ List.range 1, StrictCheckAt 21 (50+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 50 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 50) 21 50 := by decide +kernel
  exact strictAtFast_sound (row 21 50) 21 50 hvalid hfast

theorem strict_r21_part51 : ∀ i ∈ List.range 1, StrictCheckAt 21 (51+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 51 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 51) 21 51 := by decide +kernel
  exact strictAtFast_sound (row 21 51) 21 51 hvalid hfast

theorem strict_r21_part52 : ∀ i ∈ List.range 1, StrictCheckAt 21 (52+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 52 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 52) 21 52 := by decide +kernel
  exact strictAtFast_sound (row 21 52) 21 52 hvalid hfast

theorem strict_r21_part53 : ∀ i ∈ List.range 1, StrictCheckAt 21 (53+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 53 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 53) 21 53 := by decide +kernel
  exact strictAtFast_sound (row 21 53) 21 53 hvalid hfast

theorem strict_r21_part54 : ∀ i ∈ List.range 1, StrictCheckAt 21 (54+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 54 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 54) 21 54 := by decide +kernel
  exact strictAtFast_sound (row 21 54) 21 54 hvalid hfast

theorem strict_r21_part55 : ∀ i ∈ List.range 1, StrictCheckAt 21 (55+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 55 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 55) 21 55 := by decide +kernel
  exact strictAtFast_sound (row 21 55) 21 55 hvalid hfast

theorem strict_r21_part56 : ∀ i ∈ List.range 1, StrictCheckAt 21 (56+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 56 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 56) 21 56 := by decide +kernel
  exact strictAtFast_sound (row 21 56) 21 56 hvalid hfast

theorem strict_r21_part57 : ∀ i ∈ List.range 1, StrictCheckAt 21 (57+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 57 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 57) 21 57 := by decide +kernel
  exact strictAtFast_sound (row 21 57) 21 57 hvalid hfast

theorem strict_r21_part58 : ∀ i ∈ List.range 1, StrictCheckAt 21 (58+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 58 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 58) 21 58 := by decide +kernel
  exact strictAtFast_sound (row 21 58) 21 58 hvalid hfast

theorem strict_r21_part59 : ∀ i ∈ List.range 1, StrictCheckAt 21 (59+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 59 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 59) 21 59 := by decide +kernel
  exact strictAtFast_sound (row 21 59) 21 59 hvalid hfast

theorem strict_r21_part60 : ∀ i ∈ List.range 1, StrictCheckAt 21 (60+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 60 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 60) 21 60 := by decide +kernel
  exact strictAtFast_sound (row 21 60) 21 60 hvalid hfast

theorem strict_r21_part61 : ∀ i ∈ List.range 1, StrictCheckAt 21 (61+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 61 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 61) 21 61 := by decide +kernel
  exact strictAtFast_sound (row 21 61) 21 61 hvalid hfast

theorem strict_r21_part62 : ∀ i ∈ List.range 1, StrictCheckAt 21 (62+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 62 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 62) 21 62 := by decide +kernel
  exact strictAtFast_sound (row 21 62) 21 62 hvalid hfast

theorem strict_r21_part63 : ∀ i ∈ List.range 1, StrictCheckAt 21 (63+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 63 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 63) 21 63 := by decide +kernel
  exact strictAtFast_sound (row 21 63) 21 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
