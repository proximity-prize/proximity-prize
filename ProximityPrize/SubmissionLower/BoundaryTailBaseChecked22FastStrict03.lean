import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r22_part32 : ∀ i ∈ List.range 1, StrictCheckAt 22 (32+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 32 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 32) 22 32 := by decide +kernel
  exact strictAtFast_sound (row 22 32) 22 32 hvalid hfast

theorem strict_r22_part33 : ∀ i ∈ List.range 1, StrictCheckAt 22 (33+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 33 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 33) 22 33 := by decide +kernel
  exact strictAtFast_sound (row 22 33) 22 33 hvalid hfast

theorem strict_r22_part34 : ∀ i ∈ List.range 1, StrictCheckAt 22 (34+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 34 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 34) 22 34 := by decide +kernel
  exact strictAtFast_sound (row 22 34) 22 34 hvalid hfast

theorem strict_r22_part35 : ∀ i ∈ List.range 1, StrictCheckAt 22 (35+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 35 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 35) 22 35 := by decide +kernel
  exact strictAtFast_sound (row 22 35) 22 35 hvalid hfast

theorem strict_r22_part36 : ∀ i ∈ List.range 1, StrictCheckAt 22 (36+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 36 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 36) 22 36 := by decide +kernel
  exact strictAtFast_sound (row 22 36) 22 36 hvalid hfast

theorem strict_r22_part37 : ∀ i ∈ List.range 1, StrictCheckAt 22 (37+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 37 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 37) 22 37 := by decide +kernel
  exact strictAtFast_sound (row 22 37) 22 37 hvalid hfast

theorem strict_r22_part38 : ∀ i ∈ List.range 1, StrictCheckAt 22 (38+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 38 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 38) 22 38 := by decide +kernel
  exact strictAtFast_sound (row 22 38) 22 38 hvalid hfast

theorem strict_r22_part39 : ∀ i ∈ List.range 1, StrictCheckAt 22 (39+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 39 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 39) 22 39 := by decide +kernel
  exact strictAtFast_sound (row 22 39) 22 39 hvalid hfast

theorem strict_r22_part40 : ∀ i ∈ List.range 1, StrictCheckAt 22 (40+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 40 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 40) 22 40 := by decide +kernel
  exact strictAtFast_sound (row 22 40) 22 40 hvalid hfast

theorem strict_r22_part41 : ∀ i ∈ List.range 1, StrictCheckAt 22 (41+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 41 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 41) 22 41 := by decide +kernel
  exact strictAtFast_sound (row 22 41) 22 41 hvalid hfast

theorem strict_r22_part42 : ∀ i ∈ List.range 1, StrictCheckAt 22 (42+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 42 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 42) 22 42 := by decide +kernel
  exact strictAtFast_sound (row 22 42) 22 42 hvalid hfast

theorem strict_r22_part43 : ∀ i ∈ List.range 1, StrictCheckAt 22 (43+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 43 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 43) 22 43 := by decide +kernel
  exact strictAtFast_sound (row 22 43) 22 43 hvalid hfast

theorem strict_r22_part44 : ∀ i ∈ List.range 1, StrictCheckAt 22 (44+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 44 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 44) 22 44 := by decide +kernel
  exact strictAtFast_sound (row 22 44) 22 44 hvalid hfast

theorem strict_r22_part45 : ∀ i ∈ List.range 1, StrictCheckAt 22 (45+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 45 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 45) 22 45 := by decide +kernel
  exact strictAtFast_sound (row 22 45) 22 45 hvalid hfast

theorem strict_r22_part46 : ∀ i ∈ List.range 1, StrictCheckAt 22 (46+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 46 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 46) 22 46 := by decide +kernel
  exact strictAtFast_sound (row 22 46) 22 46 hvalid hfast

theorem strict_r22_part47 : ∀ i ∈ List.range 1, StrictCheckAt 22 (47+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 22 47 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 22 47) 22 47 := by decide +kernel
  exact strictAtFast_sound (row 22 47) 22 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
