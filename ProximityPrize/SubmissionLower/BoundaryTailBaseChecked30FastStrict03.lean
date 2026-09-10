import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r30_part32 : ∀ i ∈ List.range 1, StrictCheckAt 30 (32+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 32 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 32) 30 32 := by decide +kernel
  exact strictAtFast_sound (row 30 32) 30 32 hvalid hfast

theorem strict_r30_part33 : ∀ i ∈ List.range 1, StrictCheckAt 30 (33+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 33 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 33) 30 33 := by decide +kernel
  exact strictAtFast_sound (row 30 33) 30 33 hvalid hfast

theorem strict_r30_part34 : ∀ i ∈ List.range 1, StrictCheckAt 30 (34+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 34 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 34) 30 34 := by decide +kernel
  exact strictAtFast_sound (row 30 34) 30 34 hvalid hfast

theorem strict_r30_part35 : ∀ i ∈ List.range 1, StrictCheckAt 30 (35+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 35 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 35) 30 35 := by decide +kernel
  exact strictAtFast_sound (row 30 35) 30 35 hvalid hfast

theorem strict_r30_part36 : ∀ i ∈ List.range 1, StrictCheckAt 30 (36+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 36 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 36) 30 36 := by decide +kernel
  exact strictAtFast_sound (row 30 36) 30 36 hvalid hfast

theorem strict_r30_part37 : ∀ i ∈ List.range 1, StrictCheckAt 30 (37+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 37 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 37) 30 37 := by decide +kernel
  exact strictAtFast_sound (row 30 37) 30 37 hvalid hfast

theorem strict_r30_part38 : ∀ i ∈ List.range 1, StrictCheckAt 30 (38+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 38 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 38) 30 38 := by decide +kernel
  exact strictAtFast_sound (row 30 38) 30 38 hvalid hfast

theorem strict_r30_part39 : ∀ i ∈ List.range 1, StrictCheckAt 30 (39+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 39 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 39) 30 39 := by decide +kernel
  exact strictAtFast_sound (row 30 39) 30 39 hvalid hfast

theorem strict_r30_part40 : ∀ i ∈ List.range 1, StrictCheckAt 30 (40+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 40 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 40) 30 40 := by decide +kernel
  exact strictAtFast_sound (row 30 40) 30 40 hvalid hfast

theorem strict_r30_part41 : ∀ i ∈ List.range 1, StrictCheckAt 30 (41+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 41 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 41) 30 41 := by decide +kernel
  exact strictAtFast_sound (row 30 41) 30 41 hvalid hfast

theorem strict_r30_part42 : ∀ i ∈ List.range 1, StrictCheckAt 30 (42+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 42 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 42) 30 42 := by decide +kernel
  exact strictAtFast_sound (row 30 42) 30 42 hvalid hfast

theorem strict_r30_part43 : ∀ i ∈ List.range 1, StrictCheckAt 30 (43+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 43 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 43) 30 43 := by decide +kernel
  exact strictAtFast_sound (row 30 43) 30 43 hvalid hfast

theorem strict_r30_part44 : ∀ i ∈ List.range 1, StrictCheckAt 30 (44+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 44 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 44) 30 44 := by decide +kernel
  exact strictAtFast_sound (row 30 44) 30 44 hvalid hfast

theorem strict_r30_part45 : ∀ i ∈ List.range 1, StrictCheckAt 30 (45+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 45 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 45) 30 45 := by decide +kernel
  exact strictAtFast_sound (row 30 45) 30 45 hvalid hfast

theorem strict_r30_part46 : ∀ i ∈ List.range 1, StrictCheckAt 30 (46+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 46 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 46) 30 46 := by decide +kernel
  exact strictAtFast_sound (row 30 46) 30 46 hvalid hfast

theorem strict_r30_part47 : ∀ i ∈ List.range 1, StrictCheckAt 30 (47+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 30 47 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 30 47) 30 47 := by decide +kernel
  exact strictAtFast_sound (row 30 47) 30 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
