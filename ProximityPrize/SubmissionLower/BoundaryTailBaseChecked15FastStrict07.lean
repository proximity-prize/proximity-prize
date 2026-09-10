import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r15_part96 : ∀ i ∈ List.range 1, StrictCheckAt 15 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 96) 15 96 := by decide +kernel
  exact strictAtFast_sound (row 15 96) 15 96 hvalid hfast

theorem strict_r15_part97 : ∀ i ∈ List.range 1, StrictCheckAt 15 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 97) 15 97 := by decide +kernel
  exact strictAtFast_sound (row 15 97) 15 97 hvalid hfast

theorem strict_r15_part98 : ∀ i ∈ List.range 1, StrictCheckAt 15 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 98) 15 98 := by decide +kernel
  exact strictAtFast_sound (row 15 98) 15 98 hvalid hfast

theorem strict_r15_part99 : ∀ i ∈ List.range 1, StrictCheckAt 15 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 99) 15 99 := by decide +kernel
  exact strictAtFast_sound (row 15 99) 15 99 hvalid hfast

theorem strict_r15_part100 : ∀ i ∈ List.range 1, StrictCheckAt 15 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 100) 15 100 := by decide +kernel
  exact strictAtFast_sound (row 15 100) 15 100 hvalid hfast

theorem strict_r15_part101 : ∀ i ∈ List.range 1, StrictCheckAt 15 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 101) 15 101 := by decide +kernel
  exact strictAtFast_sound (row 15 101) 15 101 hvalid hfast

theorem strict_r15_part102 : ∀ i ∈ List.range 1, StrictCheckAt 15 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 102) 15 102 := by decide +kernel
  exact strictAtFast_sound (row 15 102) 15 102 hvalid hfast

theorem strict_r15_part103 : ∀ i ∈ List.range 1, StrictCheckAt 15 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 103) 15 103 := by decide +kernel
  exact strictAtFast_sound (row 15 103) 15 103 hvalid hfast

theorem strict_r15_part104 : ∀ i ∈ List.range 1, StrictCheckAt 15 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 104) 15 104 := by decide +kernel
  exact strictAtFast_sound (row 15 104) 15 104 hvalid hfast

theorem strict_r15_part105 : ∀ i ∈ List.range 1, StrictCheckAt 15 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 105) 15 105 := by decide +kernel
  exact strictAtFast_sound (row 15 105) 15 105 hvalid hfast

theorem strict_r15_part106 : ∀ i ∈ List.range 1, StrictCheckAt 15 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 106) 15 106 := by decide +kernel
  exact strictAtFast_sound (row 15 106) 15 106 hvalid hfast

theorem strict_r15_part107 : ∀ i ∈ List.range 1, StrictCheckAt 15 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 107) 15 107 := by decide +kernel
  exact strictAtFast_sound (row 15 107) 15 107 hvalid hfast

theorem strict_r15_part108 : ∀ i ∈ List.range 1, StrictCheckAt 15 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 108) 15 108 := by decide +kernel
  exact strictAtFast_sound (row 15 108) 15 108 hvalid hfast

theorem strict_r15_part109 : ∀ i ∈ List.range 1, StrictCheckAt 15 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 109) 15 109 := by decide +kernel
  exact strictAtFast_sound (row 15 109) 15 109 hvalid hfast

theorem strict_r15_part110 : ∀ i ∈ List.range 1, StrictCheckAt 15 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 110) 15 110 := by decide +kernel
  exact strictAtFast_sound (row 15 110) 15 110 hvalid hfast

theorem strict_r15_part111 : ∀ i ∈ List.range 1, StrictCheckAt 15 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 15 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 15 111) 15 111 := by decide +kernel
  exact strictAtFast_sound (row 15 111) 15 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
