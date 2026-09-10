import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r20_part96 : ∀ i ∈ List.range 1, StrictCheckAt 20 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 96) 20 96 := by decide +kernel
  exact strictAtFast_sound (row 20 96) 20 96 hvalid hfast

theorem strict_r20_part97 : ∀ i ∈ List.range 1, StrictCheckAt 20 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 97) 20 97 := by decide +kernel
  exact strictAtFast_sound (row 20 97) 20 97 hvalid hfast

theorem strict_r20_part98 : ∀ i ∈ List.range 1, StrictCheckAt 20 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 98) 20 98 := by decide +kernel
  exact strictAtFast_sound (row 20 98) 20 98 hvalid hfast

theorem strict_r20_part99 : ∀ i ∈ List.range 1, StrictCheckAt 20 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 99) 20 99 := by decide +kernel
  exact strictAtFast_sound (row 20 99) 20 99 hvalid hfast

theorem strict_r20_part100 : ∀ i ∈ List.range 1, StrictCheckAt 20 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 100) 20 100 := by decide +kernel
  exact strictAtFast_sound (row 20 100) 20 100 hvalid hfast

theorem strict_r20_part101 : ∀ i ∈ List.range 1, StrictCheckAt 20 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 101) 20 101 := by decide +kernel
  exact strictAtFast_sound (row 20 101) 20 101 hvalid hfast

theorem strict_r20_part102 : ∀ i ∈ List.range 1, StrictCheckAt 20 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 102) 20 102 := by decide +kernel
  exact strictAtFast_sound (row 20 102) 20 102 hvalid hfast

theorem strict_r20_part103 : ∀ i ∈ List.range 1, StrictCheckAt 20 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 103) 20 103 := by decide +kernel
  exact strictAtFast_sound (row 20 103) 20 103 hvalid hfast

theorem strict_r20_part104 : ∀ i ∈ List.range 1, StrictCheckAt 20 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 104) 20 104 := by decide +kernel
  exact strictAtFast_sound (row 20 104) 20 104 hvalid hfast

theorem strict_r20_part105 : ∀ i ∈ List.range 1, StrictCheckAt 20 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 105) 20 105 := by decide +kernel
  exact strictAtFast_sound (row 20 105) 20 105 hvalid hfast

theorem strict_r20_part106 : ∀ i ∈ List.range 1, StrictCheckAt 20 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 106) 20 106 := by decide +kernel
  exact strictAtFast_sound (row 20 106) 20 106 hvalid hfast

theorem strict_r20_part107 : ∀ i ∈ List.range 1, StrictCheckAt 20 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 107) 20 107 := by decide +kernel
  exact strictAtFast_sound (row 20 107) 20 107 hvalid hfast

theorem strict_r20_part108 : ∀ i ∈ List.range 1, StrictCheckAt 20 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 108) 20 108 := by decide +kernel
  exact strictAtFast_sound (row 20 108) 20 108 hvalid hfast

theorem strict_r20_part109 : ∀ i ∈ List.range 1, StrictCheckAt 20 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 109) 20 109 := by decide +kernel
  exact strictAtFast_sound (row 20 109) 20 109 hvalid hfast

theorem strict_r20_part110 : ∀ i ∈ List.range 1, StrictCheckAt 20 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 110) 20 110 := by decide +kernel
  exact strictAtFast_sound (row 20 110) 20 110 hvalid hfast

theorem strict_r20_part111 : ∀ i ∈ List.range 1, StrictCheckAt 20 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 111) 20 111 := by decide +kernel
  exact strictAtFast_sound (row 20 111) 20 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
