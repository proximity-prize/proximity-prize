import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r28_part96 : ∀ i ∈ List.range 1, StrictCheckAt 28 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 96) 28 96 := by decide +kernel
  exact strictAtFast_sound (row 28 96) 28 96 hvalid hfast

theorem strict_r28_part97 : ∀ i ∈ List.range 1, StrictCheckAt 28 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 97) 28 97 := by decide +kernel
  exact strictAtFast_sound (row 28 97) 28 97 hvalid hfast

theorem strict_r28_part98 : ∀ i ∈ List.range 1, StrictCheckAt 28 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 98) 28 98 := by decide +kernel
  exact strictAtFast_sound (row 28 98) 28 98 hvalid hfast

theorem strict_r28_part99 : ∀ i ∈ List.range 1, StrictCheckAt 28 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 99) 28 99 := by decide +kernel
  exact strictAtFast_sound (row 28 99) 28 99 hvalid hfast

theorem strict_r28_part100 : ∀ i ∈ List.range 1, StrictCheckAt 28 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 100) 28 100 := by decide +kernel
  exact strictAtFast_sound (row 28 100) 28 100 hvalid hfast

theorem strict_r28_part101 : ∀ i ∈ List.range 1, StrictCheckAt 28 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 101) 28 101 := by decide +kernel
  exact strictAtFast_sound (row 28 101) 28 101 hvalid hfast

theorem strict_r28_part102 : ∀ i ∈ List.range 1, StrictCheckAt 28 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 102) 28 102 := by decide +kernel
  exact strictAtFast_sound (row 28 102) 28 102 hvalid hfast

theorem strict_r28_part103 : ∀ i ∈ List.range 1, StrictCheckAt 28 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 103) 28 103 := by decide +kernel
  exact strictAtFast_sound (row 28 103) 28 103 hvalid hfast

theorem strict_r28_part104 : ∀ i ∈ List.range 1, StrictCheckAt 28 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 104) 28 104 := by decide +kernel
  exact strictAtFast_sound (row 28 104) 28 104 hvalid hfast

theorem strict_r28_part105 : ∀ i ∈ List.range 1, StrictCheckAt 28 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 105) 28 105 := by decide +kernel
  exact strictAtFast_sound (row 28 105) 28 105 hvalid hfast

theorem strict_r28_part106 : ∀ i ∈ List.range 1, StrictCheckAt 28 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 106) 28 106 := by decide +kernel
  exact strictAtFast_sound (row 28 106) 28 106 hvalid hfast

theorem strict_r28_part107 : ∀ i ∈ List.range 1, StrictCheckAt 28 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 107) 28 107 := by decide +kernel
  exact strictAtFast_sound (row 28 107) 28 107 hvalid hfast

theorem strict_r28_part108 : ∀ i ∈ List.range 1, StrictCheckAt 28 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 108) 28 108 := by decide +kernel
  exact strictAtFast_sound (row 28 108) 28 108 hvalid hfast

theorem strict_r28_part109 : ∀ i ∈ List.range 1, StrictCheckAt 28 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 109) 28 109 := by decide +kernel
  exact strictAtFast_sound (row 28 109) 28 109 hvalid hfast

theorem strict_r28_part110 : ∀ i ∈ List.range 1, StrictCheckAt 28 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 110) 28 110 := by decide +kernel
  exact strictAtFast_sound (row 28 110) 28 110 hvalid hfast

theorem strict_r28_part111 : ∀ i ∈ List.range 1, StrictCheckAt 28 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 28 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 28 111) 28 111 := by decide +kernel
  exact strictAtFast_sound (row 28 111) 28 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
