import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r25_part96 : ∀ i ∈ List.range 1, StrictCheckAt 25 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 96) 25 96 := by decide +kernel
  exact strictAtFast_sound (row 25 96) 25 96 hvalid hfast

theorem strict_r25_part97 : ∀ i ∈ List.range 1, StrictCheckAt 25 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 97) 25 97 := by decide +kernel
  exact strictAtFast_sound (row 25 97) 25 97 hvalid hfast

theorem strict_r25_part98 : ∀ i ∈ List.range 1, StrictCheckAt 25 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 98) 25 98 := by decide +kernel
  exact strictAtFast_sound (row 25 98) 25 98 hvalid hfast

theorem strict_r25_part99 : ∀ i ∈ List.range 1, StrictCheckAt 25 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 99) 25 99 := by decide +kernel
  exact strictAtFast_sound (row 25 99) 25 99 hvalid hfast

theorem strict_r25_part100 : ∀ i ∈ List.range 1, StrictCheckAt 25 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 100) 25 100 := by decide +kernel
  exact strictAtFast_sound (row 25 100) 25 100 hvalid hfast

theorem strict_r25_part101 : ∀ i ∈ List.range 1, StrictCheckAt 25 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 101) 25 101 := by decide +kernel
  exact strictAtFast_sound (row 25 101) 25 101 hvalid hfast

theorem strict_r25_part102 : ∀ i ∈ List.range 1, StrictCheckAt 25 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 102) 25 102 := by decide +kernel
  exact strictAtFast_sound (row 25 102) 25 102 hvalid hfast

theorem strict_r25_part103 : ∀ i ∈ List.range 1, StrictCheckAt 25 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 103) 25 103 := by decide +kernel
  exact strictAtFast_sound (row 25 103) 25 103 hvalid hfast

theorem strict_r25_part104 : ∀ i ∈ List.range 1, StrictCheckAt 25 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 104) 25 104 := by decide +kernel
  exact strictAtFast_sound (row 25 104) 25 104 hvalid hfast

theorem strict_r25_part105 : ∀ i ∈ List.range 1, StrictCheckAt 25 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 105) 25 105 := by decide +kernel
  exact strictAtFast_sound (row 25 105) 25 105 hvalid hfast

theorem strict_r25_part106 : ∀ i ∈ List.range 1, StrictCheckAt 25 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 106) 25 106 := by decide +kernel
  exact strictAtFast_sound (row 25 106) 25 106 hvalid hfast

theorem strict_r25_part107 : ∀ i ∈ List.range 1, StrictCheckAt 25 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 107) 25 107 := by decide +kernel
  exact strictAtFast_sound (row 25 107) 25 107 hvalid hfast

theorem strict_r25_part108 : ∀ i ∈ List.range 1, StrictCheckAt 25 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 108) 25 108 := by decide +kernel
  exact strictAtFast_sound (row 25 108) 25 108 hvalid hfast

theorem strict_r25_part109 : ∀ i ∈ List.range 1, StrictCheckAt 25 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 109) 25 109 := by decide +kernel
  exact strictAtFast_sound (row 25 109) 25 109 hvalid hfast

theorem strict_r25_part110 : ∀ i ∈ List.range 1, StrictCheckAt 25 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 110) 25 110 := by decide +kernel
  exact strictAtFast_sound (row 25 110) 25 110 hvalid hfast

theorem strict_r25_part111 : ∀ i ∈ List.range 1, StrictCheckAt 25 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 25 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 25 111) 25 111 := by decide +kernel
  exact strictAtFast_sound (row 25 111) 25 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
