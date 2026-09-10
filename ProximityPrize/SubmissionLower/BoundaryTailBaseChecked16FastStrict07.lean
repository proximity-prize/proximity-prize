import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r16_part96 : ∀ i ∈ List.range 1, StrictCheckAt 16 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 96) 16 96 := by decide +kernel
  exact strictAtFast_sound (row 16 96) 16 96 hvalid hfast

theorem strict_r16_part97 : ∀ i ∈ List.range 1, StrictCheckAt 16 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 97) 16 97 := by decide +kernel
  exact strictAtFast_sound (row 16 97) 16 97 hvalid hfast

theorem strict_r16_part98 : ∀ i ∈ List.range 1, StrictCheckAt 16 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 98) 16 98 := by decide +kernel
  exact strictAtFast_sound (row 16 98) 16 98 hvalid hfast

theorem strict_r16_part99 : ∀ i ∈ List.range 1, StrictCheckAt 16 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 99) 16 99 := by decide +kernel
  exact strictAtFast_sound (row 16 99) 16 99 hvalid hfast

theorem strict_r16_part100 : ∀ i ∈ List.range 1, StrictCheckAt 16 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 100) 16 100 := by decide +kernel
  exact strictAtFast_sound (row 16 100) 16 100 hvalid hfast

theorem strict_r16_part101 : ∀ i ∈ List.range 1, StrictCheckAt 16 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 101) 16 101 := by decide +kernel
  exact strictAtFast_sound (row 16 101) 16 101 hvalid hfast

theorem strict_r16_part102 : ∀ i ∈ List.range 1, StrictCheckAt 16 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 102) 16 102 := by decide +kernel
  exact strictAtFast_sound (row 16 102) 16 102 hvalid hfast

theorem strict_r16_part103 : ∀ i ∈ List.range 1, StrictCheckAt 16 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 103) 16 103 := by decide +kernel
  exact strictAtFast_sound (row 16 103) 16 103 hvalid hfast

theorem strict_r16_part104 : ∀ i ∈ List.range 1, StrictCheckAt 16 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 104) 16 104 := by decide +kernel
  exact strictAtFast_sound (row 16 104) 16 104 hvalid hfast

theorem strict_r16_part105 : ∀ i ∈ List.range 1, StrictCheckAt 16 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 105) 16 105 := by decide +kernel
  exact strictAtFast_sound (row 16 105) 16 105 hvalid hfast

theorem strict_r16_part106 : ∀ i ∈ List.range 1, StrictCheckAt 16 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 106) 16 106 := by decide +kernel
  exact strictAtFast_sound (row 16 106) 16 106 hvalid hfast

theorem strict_r16_part107 : ∀ i ∈ List.range 1, StrictCheckAt 16 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 107) 16 107 := by decide +kernel
  exact strictAtFast_sound (row 16 107) 16 107 hvalid hfast

theorem strict_r16_part108 : ∀ i ∈ List.range 1, StrictCheckAt 16 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 108) 16 108 := by decide +kernel
  exact strictAtFast_sound (row 16 108) 16 108 hvalid hfast

theorem strict_r16_part109 : ∀ i ∈ List.range 1, StrictCheckAt 16 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 109) 16 109 := by decide +kernel
  exact strictAtFast_sound (row 16 109) 16 109 hvalid hfast

theorem strict_r16_part110 : ∀ i ∈ List.range 1, StrictCheckAt 16 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 110) 16 110 := by decide +kernel
  exact strictAtFast_sound (row 16 110) 16 110 hvalid hfast

theorem strict_r16_part111 : ∀ i ∈ List.range 1, StrictCheckAt 16 (111+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 16 111 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 16 111) 16 111 := by decide +kernel
  exact strictAtFast_sound (row 16 111) 16 111 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
