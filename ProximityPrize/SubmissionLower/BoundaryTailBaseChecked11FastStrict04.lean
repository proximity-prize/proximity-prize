import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r11_part48 : ∀ i ∈ List.range 1, StrictCheckAt 11 (48+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 48 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 48) 11 48 := by decide +kernel
  exact strictAtFast_sound (row 11 48) 11 48 hvalid hfast

theorem strict_r11_part49 : ∀ i ∈ List.range 1, StrictCheckAt 11 (49+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 49 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 49) 11 49 := by decide +kernel
  exact strictAtFast_sound (row 11 49) 11 49 hvalid hfast

theorem strict_r11_part50 : ∀ i ∈ List.range 1, StrictCheckAt 11 (50+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 50 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 50) 11 50 := by decide +kernel
  exact strictAtFast_sound (row 11 50) 11 50 hvalid hfast

theorem strict_r11_part51 : ∀ i ∈ List.range 1, StrictCheckAt 11 (51+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 51 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 51) 11 51 := by decide +kernel
  exact strictAtFast_sound (row 11 51) 11 51 hvalid hfast

theorem strict_r11_part52 : ∀ i ∈ List.range 1, StrictCheckAt 11 (52+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 52 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 52) 11 52 := by decide +kernel
  exact strictAtFast_sound (row 11 52) 11 52 hvalid hfast

theorem strict_r11_part53 : ∀ i ∈ List.range 1, StrictCheckAt 11 (53+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 53 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 53) 11 53 := by decide +kernel
  exact strictAtFast_sound (row 11 53) 11 53 hvalid hfast

theorem strict_r11_part54 : ∀ i ∈ List.range 1, StrictCheckAt 11 (54+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 54 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 54) 11 54 := by decide +kernel
  exact strictAtFast_sound (row 11 54) 11 54 hvalid hfast

theorem strict_r11_part55 : ∀ i ∈ List.range 1, StrictCheckAt 11 (55+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 55 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 55) 11 55 := by decide +kernel
  exact strictAtFast_sound (row 11 55) 11 55 hvalid hfast

theorem strict_r11_part56 : ∀ i ∈ List.range 1, StrictCheckAt 11 (56+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 56 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 56) 11 56 := by decide +kernel
  exact strictAtFast_sound (row 11 56) 11 56 hvalid hfast

theorem strict_r11_part57 : ∀ i ∈ List.range 1, StrictCheckAt 11 (57+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 57 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 57) 11 57 := by decide +kernel
  exact strictAtFast_sound (row 11 57) 11 57 hvalid hfast

theorem strict_r11_part58 : ∀ i ∈ List.range 1, StrictCheckAt 11 (58+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 58 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 58) 11 58 := by decide +kernel
  exact strictAtFast_sound (row 11 58) 11 58 hvalid hfast

theorem strict_r11_part59 : ∀ i ∈ List.range 1, StrictCheckAt 11 (59+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 59 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 59) 11 59 := by decide +kernel
  exact strictAtFast_sound (row 11 59) 11 59 hvalid hfast

theorem strict_r11_part60 : ∀ i ∈ List.range 1, StrictCheckAt 11 (60+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 60 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 60) 11 60 := by decide +kernel
  exact strictAtFast_sound (row 11 60) 11 60 hvalid hfast

theorem strict_r11_part61 : ∀ i ∈ List.range 1, StrictCheckAt 11 (61+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 61 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 61) 11 61 := by decide +kernel
  exact strictAtFast_sound (row 11 61) 11 61 hvalid hfast

theorem strict_r11_part62 : ∀ i ∈ List.range 1, StrictCheckAt 11 (62+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 62 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 62) 11 62 := by decide +kernel
  exact strictAtFast_sound (row 11 62) 11 62 hvalid hfast

theorem strict_r11_part63 : ∀ i ∈ List.range 1, StrictCheckAt 11 (63+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 63 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 63) 11 63 := by decide +kernel
  exact strictAtFast_sound (row 11 63) 11 63 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
