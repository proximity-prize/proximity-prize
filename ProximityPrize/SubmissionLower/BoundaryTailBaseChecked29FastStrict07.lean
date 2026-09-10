import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29FastStrict06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r29_part96 : ∀ i ∈ List.range 1, StrictCheckAt 29 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 96 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 96) 29 96 := by decide +kernel
  exact strictAtFast_sound (row 29 96) 29 96 hvalid hfast

theorem strict_r29_part97 : ∀ i ∈ List.range 1, StrictCheckAt 29 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 97 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 97) 29 97 := by decide +kernel
  exact strictAtFast_sound (row 29 97) 29 97 hvalid hfast

theorem strict_r29_part98 : ∀ i ∈ List.range 1, StrictCheckAt 29 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 98 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 98) 29 98 := by decide +kernel
  exact strictAtFast_sound (row 29 98) 29 98 hvalid hfast

theorem strict_r29_part99 : ∀ i ∈ List.range 1, StrictCheckAt 29 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 99 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 99) 29 99 := by decide +kernel
  exact strictAtFast_sound (row 29 99) 29 99 hvalid hfast

theorem strict_r29_part100 : ∀ i ∈ List.range 1, StrictCheckAt 29 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 100 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 100) 29 100 := by decide +kernel
  exact strictAtFast_sound (row 29 100) 29 100 hvalid hfast

theorem strict_r29_part101 : ∀ i ∈ List.range 1, StrictCheckAt 29 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 101 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 101) 29 101 := by decide +kernel
  exact strictAtFast_sound (row 29 101) 29 101 hvalid hfast

theorem strict_r29_part102 : ∀ i ∈ List.range 1, StrictCheckAt 29 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 102 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 102) 29 102 := by decide +kernel
  exact strictAtFast_sound (row 29 102) 29 102 hvalid hfast

theorem strict_r29_part103 : ∀ i ∈ List.range 1, StrictCheckAt 29 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 103 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 103) 29 103 := by decide +kernel
  exact strictAtFast_sound (row 29 103) 29 103 hvalid hfast

theorem strict_r29_part104 : ∀ i ∈ List.range 1, StrictCheckAt 29 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 104 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 104) 29 104 := by decide +kernel
  exact strictAtFast_sound (row 29 104) 29 104 hvalid hfast

theorem strict_r29_part105 : ∀ i ∈ List.range 1, StrictCheckAt 29 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 105 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 105) 29 105 := by decide +kernel
  exact strictAtFast_sound (row 29 105) 29 105 hvalid hfast

theorem strict_r29_part106 : ∀ i ∈ List.range 1, StrictCheckAt 29 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 106 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 106) 29 106 := by decide +kernel
  exact strictAtFast_sound (row 29 106) 29 106 hvalid hfast

theorem strict_r29_part107 : ∀ i ∈ List.range 1, StrictCheckAt 29 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 107 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 107) 29 107 := by decide +kernel
  exact strictAtFast_sound (row 29 107) 29 107 hvalid hfast

theorem strict_r29_part108 : ∀ i ∈ List.range 1, StrictCheckAt 29 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 108 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 108) 29 108 := by decide +kernel
  exact strictAtFast_sound (row 29 108) 29 108 hvalid hfast

theorem strict_r29_part109 : ∀ i ∈ List.range 1, StrictCheckAt 29 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 109 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 109) 29 109 := by decide +kernel
  exact strictAtFast_sound (row 29 109) 29 109 hvalid hfast

theorem strict_r29_part110 : ∀ i ∈ List.range 1, StrictCheckAt 29 (110+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 29 110 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 29 110) 29 110 := by decide +kernel
  exact strictAtFast_sound (row 29 110) 29 110 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
