import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r7_part96 : ∀ i ∈ List.range 1, StrictCheckAt 7 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 96) 7 96 := by decide +kernel
  exact strictAtFast_sound (row 7 96) 7 96 hvalid hfast

theorem strict_r7_part97 : ∀ i ∈ List.range 1, StrictCheckAt 7 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 97) 7 97 := by decide +kernel
  exact strictAtFast_sound (row 7 97) 7 97 hvalid hfast

theorem strict_r7_part98 : ∀ i ∈ List.range 1, StrictCheckAt 7 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 98) 7 98 := by decide +kernel
  exact strictAtFast_sound (row 7 98) 7 98 hvalid hfast

theorem strict_r7_part99 : ∀ i ∈ List.range 1, StrictCheckAt 7 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 99) 7 99 := by decide +kernel
  exact strictAtFast_sound (row 7 99) 7 99 hvalid hfast

theorem strict_r7_part100 : ∀ i ∈ List.range 1, StrictCheckAt 7 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 100) 7 100 := by decide +kernel
  exact strictAtFast_sound (row 7 100) 7 100 hvalid hfast

theorem strict_r7_part101 : ∀ i ∈ List.range 1, StrictCheckAt 7 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 101) 7 101 := by decide +kernel
  exact strictAtFast_sound (row 7 101) 7 101 hvalid hfast

theorem strict_r7_part102 : ∀ i ∈ List.range 1, StrictCheckAt 7 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 102) 7 102 := by decide +kernel
  exact strictAtFast_sound (row 7 102) 7 102 hvalid hfast

theorem strict_r7_part103 : ∀ i ∈ List.range 1, StrictCheckAt 7 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 103) 7 103 := by decide +kernel
  exact strictAtFast_sound (row 7 103) 7 103 hvalid hfast

theorem strict_r7_part104 : ∀ i ∈ List.range 1, StrictCheckAt 7 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 104) 7 104 := by decide +kernel
  exact strictAtFast_sound (row 7 104) 7 104 hvalid hfast

theorem strict_r7_part105 : ∀ i ∈ List.range 1, StrictCheckAt 7 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 105) 7 105 := by decide +kernel
  exact strictAtFast_sound (row 7 105) 7 105 hvalid hfast

theorem strict_r7_part106 : ∀ i ∈ List.range 1, StrictCheckAt 7 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 106) 7 106 := by decide +kernel
  exact strictAtFast_sound (row 7 106) 7 106 hvalid hfast

theorem strict_r7_part107 : ∀ i ∈ List.range 1, StrictCheckAt 7 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 107) 7 107 := by decide +kernel
  exact strictAtFast_sound (row 7 107) 7 107 hvalid hfast

theorem strict_r7_part108 : ∀ i ∈ List.range 1, StrictCheckAt 7 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 108) 7 108 := by decide +kernel
  exact strictAtFast_sound (row 7 108) 7 108 hvalid hfast

theorem strict_r7_part109 : ∀ i ∈ List.range 1, StrictCheckAt 7 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 109) 7 109 := by decide +kernel
  exact strictAtFast_sound (row 7 109) 7 109 hvalid hfast

theorem strict_r7_part110 : ∀ i ∈ List.range 1, StrictCheckAt 7 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 110) 7 110 := by decide +kernel
  exact strictAtFast_sound (row 7 110) 7 110 hvalid hfast

theorem strict_r7_part111 : ∀ i ∈ List.range 1, StrictCheckAt 7 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 7 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 7 111) 7 111 := by decide +kernel
  exact strictAtFast_sound (row 7 111) 7 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
