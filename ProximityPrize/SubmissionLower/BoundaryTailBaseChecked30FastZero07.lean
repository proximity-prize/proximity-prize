import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastZero06

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem zero_r30_part96 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (96+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 96 := by decide +kernel
  exact zeroAtFast_sound 30 96 hfast

theorem zero_r30_part97 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (97+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 97 := by decide +kernel
  exact zeroAtFast_sound 30 97 hfast

theorem zero_r30_part98 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (98+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 98 := by decide +kernel
  exact zeroAtFast_sound 30 98 hfast

theorem zero_r30_part99 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (99+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 99 := by decide +kernel
  exact zeroAtFast_sound 30 99 hfast

theorem zero_r30_part100 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (100+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 100 := by decide +kernel
  exact zeroAtFast_sound 30 100 hfast

theorem zero_r30_part101 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (101+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 101 := by decide +kernel
  exact zeroAtFast_sound 30 101 hfast

theorem zero_r30_part102 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (102+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 102 := by decide +kernel
  exact zeroAtFast_sound 30 102 hfast

theorem zero_r30_part103 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (103+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 103 := by decide +kernel
  exact zeroAtFast_sound 30 103 hfast

theorem zero_r30_part104 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (104+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 104 := by decide +kernel
  exact zeroAtFast_sound 30 104 hfast

theorem zero_r30_part105 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (105+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 105 := by decide +kernel
  exact zeroAtFast_sound 30 105 hfast

theorem zero_r30_part106 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (106+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 106 := by decide +kernel
  exact zeroAtFast_sound 30 106 hfast

theorem zero_r30_part107 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (107+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 107 := by decide +kernel
  exact zeroAtFast_sound 30 107 hfast

theorem zero_r30_part108 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (108+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 108 := by decide +kernel
  exact zeroAtFast_sound 30 108 hfast

theorem zero_r30_part109 : ∀ i ∈ List.range 1, ZeroCheckAt 30 (109+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hfast : ZeroAtFast 30 109 := by decide +kernel
  exact zeroAtFast_sound 30 109 hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
