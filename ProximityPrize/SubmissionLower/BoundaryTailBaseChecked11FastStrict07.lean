import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r11_part96 : ∀ i ∈ List.range 1, StrictCheckAt 11 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 96) 11 96 := by decide +kernel
  exact strictAtFast_sound (row 11 96) 11 96 hvalid hfast

theorem strict_r11_part97 : ∀ i ∈ List.range 1, StrictCheckAt 11 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 97) 11 97 := by decide +kernel
  exact strictAtFast_sound (row 11 97) 11 97 hvalid hfast

theorem strict_r11_part98 : ∀ i ∈ List.range 1, StrictCheckAt 11 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 98) 11 98 := by decide +kernel
  exact strictAtFast_sound (row 11 98) 11 98 hvalid hfast

theorem strict_r11_part99 : ∀ i ∈ List.range 1, StrictCheckAt 11 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 99) 11 99 := by decide +kernel
  exact strictAtFast_sound (row 11 99) 11 99 hvalid hfast

theorem strict_r11_part100 : ∀ i ∈ List.range 1, StrictCheckAt 11 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 100) 11 100 := by decide +kernel
  exact strictAtFast_sound (row 11 100) 11 100 hvalid hfast

theorem strict_r11_part101 : ∀ i ∈ List.range 1, StrictCheckAt 11 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 101) 11 101 := by decide +kernel
  exact strictAtFast_sound (row 11 101) 11 101 hvalid hfast

theorem strict_r11_part102 : ∀ i ∈ List.range 1, StrictCheckAt 11 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 102) 11 102 := by decide +kernel
  exact strictAtFast_sound (row 11 102) 11 102 hvalid hfast

theorem strict_r11_part103 : ∀ i ∈ List.range 1, StrictCheckAt 11 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 103) 11 103 := by decide +kernel
  exact strictAtFast_sound (row 11 103) 11 103 hvalid hfast

theorem strict_r11_part104 : ∀ i ∈ List.range 1, StrictCheckAt 11 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 104) 11 104 := by decide +kernel
  exact strictAtFast_sound (row 11 104) 11 104 hvalid hfast

theorem strict_r11_part105 : ∀ i ∈ List.range 1, StrictCheckAt 11 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 105) 11 105 := by decide +kernel
  exact strictAtFast_sound (row 11 105) 11 105 hvalid hfast

theorem strict_r11_part106 : ∀ i ∈ List.range 1, StrictCheckAt 11 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 106) 11 106 := by decide +kernel
  exact strictAtFast_sound (row 11 106) 11 106 hvalid hfast

theorem strict_r11_part107 : ∀ i ∈ List.range 1, StrictCheckAt 11 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 107) 11 107 := by decide +kernel
  exact strictAtFast_sound (row 11 107) 11 107 hvalid hfast

theorem strict_r11_part108 : ∀ i ∈ List.range 1, StrictCheckAt 11 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 108) 11 108 := by decide +kernel
  exact strictAtFast_sound (row 11 108) 11 108 hvalid hfast

theorem strict_r11_part109 : ∀ i ∈ List.range 1, StrictCheckAt 11 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 109) 11 109 := by decide +kernel
  exact strictAtFast_sound (row 11 109) 11 109 hvalid hfast

theorem strict_r11_part110 : ∀ i ∈ List.range 1, StrictCheckAt 11 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 110) 11 110 := by decide +kernel
  exact strictAtFast_sound (row 11 110) 11 110 hvalid hfast

theorem strict_r11_part111 : ∀ i ∈ List.range 1, StrictCheckAt 11 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 11 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 11 111) 11 111 := by decide +kernel
  exact strictAtFast_sound (row 11 111) 11 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
