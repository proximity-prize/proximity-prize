import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r18_part48 : ∀ i ∈ List.range 1, StrictCheckAt 18 (48+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 48 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 48) 18 48 := by decide +kernel
  exact strictAtFast_sound (row 18 48) 18 48 hvalid hfast

theorem strict_r18_part49 : ∀ i ∈ List.range 1, StrictCheckAt 18 (49+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 49 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 49) 18 49 := by decide +kernel
  exact strictAtFast_sound (row 18 49) 18 49 hvalid hfast

theorem strict_r18_part50 : ∀ i ∈ List.range 1, StrictCheckAt 18 (50+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 50 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 50) 18 50 := by decide +kernel
  exact strictAtFast_sound (row 18 50) 18 50 hvalid hfast

theorem strict_r18_part51 : ∀ i ∈ List.range 1, StrictCheckAt 18 (51+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 51 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 51) 18 51 := by decide +kernel
  exact strictAtFast_sound (row 18 51) 18 51 hvalid hfast

theorem strict_r18_part52 : ∀ i ∈ List.range 1, StrictCheckAt 18 (52+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 52 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 52) 18 52 := by decide +kernel
  exact strictAtFast_sound (row 18 52) 18 52 hvalid hfast

theorem strict_r18_part53 : ∀ i ∈ List.range 1, StrictCheckAt 18 (53+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 53 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 53) 18 53 := by decide +kernel
  exact strictAtFast_sound (row 18 53) 18 53 hvalid hfast

theorem strict_r18_part54 : ∀ i ∈ List.range 1, StrictCheckAt 18 (54+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 54 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 54) 18 54 := by decide +kernel
  exact strictAtFast_sound (row 18 54) 18 54 hvalid hfast

theorem strict_r18_part55 : ∀ i ∈ List.range 1, StrictCheckAt 18 (55+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 55 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 55) 18 55 := by decide +kernel
  exact strictAtFast_sound (row 18 55) 18 55 hvalid hfast

theorem strict_r18_part56 : ∀ i ∈ List.range 1, StrictCheckAt 18 (56+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 56 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 56) 18 56 := by decide +kernel
  exact strictAtFast_sound (row 18 56) 18 56 hvalid hfast

theorem strict_r18_part57 : ∀ i ∈ List.range 1, StrictCheckAt 18 (57+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 57 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 57) 18 57 := by decide +kernel
  exact strictAtFast_sound (row 18 57) 18 57 hvalid hfast

theorem strict_r18_part58 : ∀ i ∈ List.range 1, StrictCheckAt 18 (58+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 58 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 58) 18 58 := by decide +kernel
  exact strictAtFast_sound (row 18 58) 18 58 hvalid hfast

theorem strict_r18_part59 : ∀ i ∈ List.range 1, StrictCheckAt 18 (59+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 59 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 59) 18 59 := by decide +kernel
  exact strictAtFast_sound (row 18 59) 18 59 hvalid hfast

theorem strict_r18_part60 : ∀ i ∈ List.range 1, StrictCheckAt 18 (60+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 60 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 60) 18 60 := by decide +kernel
  exact strictAtFast_sound (row 18 60) 18 60 hvalid hfast

theorem strict_r18_part61 : ∀ i ∈ List.range 1, StrictCheckAt 18 (61+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 61 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 61) 18 61 := by decide +kernel
  exact strictAtFast_sound (row 18 61) 18 61 hvalid hfast

theorem strict_r18_part62 : ∀ i ∈ List.range 1, StrictCheckAt 18 (62+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 62 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 62) 18 62 := by decide +kernel
  exact strictAtFast_sound (row 18 62) 18 62 hvalid hfast

theorem strict_r18_part63 : ∀ i ∈ List.range 1, StrictCheckAt 18 (63+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 18 63 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 18 63) 18 63 := by decide +kernel
  exact strictAtFast_sound (row 18 63) 18 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
