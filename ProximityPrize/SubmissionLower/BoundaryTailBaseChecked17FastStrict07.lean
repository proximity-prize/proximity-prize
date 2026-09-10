import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r17_part96 : ∀ i ∈ List.range 1, StrictCheckAt 17 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 96) 17 96 := by decide +kernel
  exact strictAtFast_sound (row 17 96) 17 96 hvalid hfast

theorem strict_r17_part97 : ∀ i ∈ List.range 1, StrictCheckAt 17 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 97) 17 97 := by decide +kernel
  exact strictAtFast_sound (row 17 97) 17 97 hvalid hfast

theorem strict_r17_part98 : ∀ i ∈ List.range 1, StrictCheckAt 17 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 98) 17 98 := by decide +kernel
  exact strictAtFast_sound (row 17 98) 17 98 hvalid hfast

theorem strict_r17_part99 : ∀ i ∈ List.range 1, StrictCheckAt 17 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 99) 17 99 := by decide +kernel
  exact strictAtFast_sound (row 17 99) 17 99 hvalid hfast

theorem strict_r17_part100 : ∀ i ∈ List.range 1, StrictCheckAt 17 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 100) 17 100 := by decide +kernel
  exact strictAtFast_sound (row 17 100) 17 100 hvalid hfast

theorem strict_r17_part101 : ∀ i ∈ List.range 1, StrictCheckAt 17 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 101) 17 101 := by decide +kernel
  exact strictAtFast_sound (row 17 101) 17 101 hvalid hfast

theorem strict_r17_part102 : ∀ i ∈ List.range 1, StrictCheckAt 17 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 102) 17 102 := by decide +kernel
  exact strictAtFast_sound (row 17 102) 17 102 hvalid hfast

theorem strict_r17_part103 : ∀ i ∈ List.range 1, StrictCheckAt 17 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 103) 17 103 := by decide +kernel
  exact strictAtFast_sound (row 17 103) 17 103 hvalid hfast

theorem strict_r17_part104 : ∀ i ∈ List.range 1, StrictCheckAt 17 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 104) 17 104 := by decide +kernel
  exact strictAtFast_sound (row 17 104) 17 104 hvalid hfast

theorem strict_r17_part105 : ∀ i ∈ List.range 1, StrictCheckAt 17 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 105) 17 105 := by decide +kernel
  exact strictAtFast_sound (row 17 105) 17 105 hvalid hfast

theorem strict_r17_part106 : ∀ i ∈ List.range 1, StrictCheckAt 17 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 106) 17 106 := by decide +kernel
  exact strictAtFast_sound (row 17 106) 17 106 hvalid hfast

theorem strict_r17_part107 : ∀ i ∈ List.range 1, StrictCheckAt 17 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 107) 17 107 := by decide +kernel
  exact strictAtFast_sound (row 17 107) 17 107 hvalid hfast

theorem strict_r17_part108 : ∀ i ∈ List.range 1, StrictCheckAt 17 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 108) 17 108 := by decide +kernel
  exact strictAtFast_sound (row 17 108) 17 108 hvalid hfast

theorem strict_r17_part109 : ∀ i ∈ List.range 1, StrictCheckAt 17 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 109) 17 109 := by decide +kernel
  exact strictAtFast_sound (row 17 109) 17 109 hvalid hfast

theorem strict_r17_part110 : ∀ i ∈ List.range 1, StrictCheckAt 17 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 110) 17 110 := by decide +kernel
  exact strictAtFast_sound (row 17 110) 17 110 hvalid hfast

theorem strict_r17_part111 : ∀ i ∈ List.range 1, StrictCheckAt 17 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 111) 17 111 := by decide +kernel
  exact strictAtFast_sound (row 17 111) 17 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
