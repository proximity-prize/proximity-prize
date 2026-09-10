import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r7_part48 : ∀ i ∈ List.range 1, StrictCheckAt 7 (48+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 48 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 48) 7 48 := by decide +kernel
  exact strictAtFast_sound (row 7 48) 7 48 hvalid hfast

theorem strict_r7_part49 : ∀ i ∈ List.range 1, StrictCheckAt 7 (49+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 49 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 49) 7 49 := by decide +kernel
  exact strictAtFast_sound (row 7 49) 7 49 hvalid hfast

theorem strict_r7_part50 : ∀ i ∈ List.range 1, StrictCheckAt 7 (50+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 50 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 50) 7 50 := by decide +kernel
  exact strictAtFast_sound (row 7 50) 7 50 hvalid hfast

theorem strict_r7_part51 : ∀ i ∈ List.range 1, StrictCheckAt 7 (51+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 51 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 51) 7 51 := by decide +kernel
  exact strictAtFast_sound (row 7 51) 7 51 hvalid hfast

theorem strict_r7_part52 : ∀ i ∈ List.range 1, StrictCheckAt 7 (52+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 52 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 52) 7 52 := by decide +kernel
  exact strictAtFast_sound (row 7 52) 7 52 hvalid hfast

theorem strict_r7_part53 : ∀ i ∈ List.range 1, StrictCheckAt 7 (53+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 53 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 53) 7 53 := by decide +kernel
  exact strictAtFast_sound (row 7 53) 7 53 hvalid hfast

theorem strict_r7_part54 : ∀ i ∈ List.range 1, StrictCheckAt 7 (54+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 54 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 54) 7 54 := by decide +kernel
  exact strictAtFast_sound (row 7 54) 7 54 hvalid hfast

theorem strict_r7_part55 : ∀ i ∈ List.range 1, StrictCheckAt 7 (55+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 55 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 55) 7 55 := by decide +kernel
  exact strictAtFast_sound (row 7 55) 7 55 hvalid hfast

theorem strict_r7_part56 : ∀ i ∈ List.range 1, StrictCheckAt 7 (56+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 56 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 56) 7 56 := by decide +kernel
  exact strictAtFast_sound (row 7 56) 7 56 hvalid hfast

theorem strict_r7_part57 : ∀ i ∈ List.range 1, StrictCheckAt 7 (57+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 57 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 57) 7 57 := by decide +kernel
  exact strictAtFast_sound (row 7 57) 7 57 hvalid hfast

theorem strict_r7_part58 : ∀ i ∈ List.range 1, StrictCheckAt 7 (58+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 58 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 58) 7 58 := by decide +kernel
  exact strictAtFast_sound (row 7 58) 7 58 hvalid hfast

theorem strict_r7_part59 : ∀ i ∈ List.range 1, StrictCheckAt 7 (59+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 59 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 59) 7 59 := by decide +kernel
  exact strictAtFast_sound (row 7 59) 7 59 hvalid hfast

theorem strict_r7_part60 : ∀ i ∈ List.range 1, StrictCheckAt 7 (60+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 60 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 60) 7 60 := by decide +kernel
  exact strictAtFast_sound (row 7 60) 7 60 hvalid hfast

theorem strict_r7_part61 : ∀ i ∈ List.range 1, StrictCheckAt 7 (61+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 61 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 61) 7 61 := by decide +kernel
  exact strictAtFast_sound (row 7 61) 7 61 hvalid hfast

theorem strict_r7_part62 : ∀ i ∈ List.range 1, StrictCheckAt 7 (62+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 62 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 62) 7 62 := by decide +kernel
  exact strictAtFast_sound (row 7 62) 7 62 hvalid hfast

theorem strict_r7_part63 : ∀ i ∈ List.range 1, StrictCheckAt 7 (63+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 63 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 63) 7 63 := by decide +kernel
  exact strictAtFast_sound (row 7 63) 7 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
