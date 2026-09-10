import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r21_part96 : ∀ i ∈ List.range 1, StrictCheckAt 21 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 96) 21 96 := by decide +kernel
  exact strictAtFast_sound (row 21 96) 21 96 hvalid hfast

theorem strict_r21_part97 : ∀ i ∈ List.range 1, StrictCheckAt 21 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 97) 21 97 := by decide +kernel
  exact strictAtFast_sound (row 21 97) 21 97 hvalid hfast

theorem strict_r21_part98 : ∀ i ∈ List.range 1, StrictCheckAt 21 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 98) 21 98 := by decide +kernel
  exact strictAtFast_sound (row 21 98) 21 98 hvalid hfast

theorem strict_r21_part99 : ∀ i ∈ List.range 1, StrictCheckAt 21 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 99) 21 99 := by decide +kernel
  exact strictAtFast_sound (row 21 99) 21 99 hvalid hfast

theorem strict_r21_part100 : ∀ i ∈ List.range 1, StrictCheckAt 21 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 100) 21 100 := by decide +kernel
  exact strictAtFast_sound (row 21 100) 21 100 hvalid hfast

theorem strict_r21_part101 : ∀ i ∈ List.range 1, StrictCheckAt 21 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 101) 21 101 := by decide +kernel
  exact strictAtFast_sound (row 21 101) 21 101 hvalid hfast

theorem strict_r21_part102 : ∀ i ∈ List.range 1, StrictCheckAt 21 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 102) 21 102 := by decide +kernel
  exact strictAtFast_sound (row 21 102) 21 102 hvalid hfast

theorem strict_r21_part103 : ∀ i ∈ List.range 1, StrictCheckAt 21 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 103) 21 103 := by decide +kernel
  exact strictAtFast_sound (row 21 103) 21 103 hvalid hfast

theorem strict_r21_part104 : ∀ i ∈ List.range 1, StrictCheckAt 21 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 104) 21 104 := by decide +kernel
  exact strictAtFast_sound (row 21 104) 21 104 hvalid hfast

theorem strict_r21_part105 : ∀ i ∈ List.range 1, StrictCheckAt 21 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 105) 21 105 := by decide +kernel
  exact strictAtFast_sound (row 21 105) 21 105 hvalid hfast

theorem strict_r21_part106 : ∀ i ∈ List.range 1, StrictCheckAt 21 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 106) 21 106 := by decide +kernel
  exact strictAtFast_sound (row 21 106) 21 106 hvalid hfast

theorem strict_r21_part107 : ∀ i ∈ List.range 1, StrictCheckAt 21 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 107) 21 107 := by decide +kernel
  exact strictAtFast_sound (row 21 107) 21 107 hvalid hfast

theorem strict_r21_part108 : ∀ i ∈ List.range 1, StrictCheckAt 21 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 108) 21 108 := by decide +kernel
  exact strictAtFast_sound (row 21 108) 21 108 hvalid hfast

theorem strict_r21_part109 : ∀ i ∈ List.range 1, StrictCheckAt 21 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 109) 21 109 := by decide +kernel
  exact strictAtFast_sound (row 21 109) 21 109 hvalid hfast

theorem strict_r21_part110 : ∀ i ∈ List.range 1, StrictCheckAt 21 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 110) 21 110 := by decide +kernel
  exact strictAtFast_sound (row 21 110) 21 110 hvalid hfast

theorem strict_r21_part111 : ∀ i ∈ List.range 1, StrictCheckAt 21 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 21 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 21 111) 21 111 := by decide +kernel
  exact strictAtFast_sound (row 21 111) 21 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
