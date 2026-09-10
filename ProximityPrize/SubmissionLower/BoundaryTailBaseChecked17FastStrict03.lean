import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r17_part32 : ∀ i ∈ List.range 1, StrictCheckAt 17 (32+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 32 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 32) 17 32 := by decide +kernel
  exact strictAtFast_sound (row 17 32) 17 32 hvalid hfast

theorem strict_r17_part33 : ∀ i ∈ List.range 1, StrictCheckAt 17 (33+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 33 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 33) 17 33 := by decide +kernel
  exact strictAtFast_sound (row 17 33) 17 33 hvalid hfast

theorem strict_r17_part34 : ∀ i ∈ List.range 1, StrictCheckAt 17 (34+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 34 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 34) 17 34 := by decide +kernel
  exact strictAtFast_sound (row 17 34) 17 34 hvalid hfast

theorem strict_r17_part35 : ∀ i ∈ List.range 1, StrictCheckAt 17 (35+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 35 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 35) 17 35 := by decide +kernel
  exact strictAtFast_sound (row 17 35) 17 35 hvalid hfast

theorem strict_r17_part36 : ∀ i ∈ List.range 1, StrictCheckAt 17 (36+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 36 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 36) 17 36 := by decide +kernel
  exact strictAtFast_sound (row 17 36) 17 36 hvalid hfast

theorem strict_r17_part37 : ∀ i ∈ List.range 1, StrictCheckAt 17 (37+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 37 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 37) 17 37 := by decide +kernel
  exact strictAtFast_sound (row 17 37) 17 37 hvalid hfast

theorem strict_r17_part38 : ∀ i ∈ List.range 1, StrictCheckAt 17 (38+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 38 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 38) 17 38 := by decide +kernel
  exact strictAtFast_sound (row 17 38) 17 38 hvalid hfast

theorem strict_r17_part39 : ∀ i ∈ List.range 1, StrictCheckAt 17 (39+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 39 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 39) 17 39 := by decide +kernel
  exact strictAtFast_sound (row 17 39) 17 39 hvalid hfast

theorem strict_r17_part40 : ∀ i ∈ List.range 1, StrictCheckAt 17 (40+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 40 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 40) 17 40 := by decide +kernel
  exact strictAtFast_sound (row 17 40) 17 40 hvalid hfast

theorem strict_r17_part41 : ∀ i ∈ List.range 1, StrictCheckAt 17 (41+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 41 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 41) 17 41 := by decide +kernel
  exact strictAtFast_sound (row 17 41) 17 41 hvalid hfast

theorem strict_r17_part42 : ∀ i ∈ List.range 1, StrictCheckAt 17 (42+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 42 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 42) 17 42 := by decide +kernel
  exact strictAtFast_sound (row 17 42) 17 42 hvalid hfast

theorem strict_r17_part43 : ∀ i ∈ List.range 1, StrictCheckAt 17 (43+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 43 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 43) 17 43 := by decide +kernel
  exact strictAtFast_sound (row 17 43) 17 43 hvalid hfast

theorem strict_r17_part44 : ∀ i ∈ List.range 1, StrictCheckAt 17 (44+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 44 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 44) 17 44 := by decide +kernel
  exact strictAtFast_sound (row 17 44) 17 44 hvalid hfast

theorem strict_r17_part45 : ∀ i ∈ List.range 1, StrictCheckAt 17 (45+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 45 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 45) 17 45 := by decide +kernel
  exact strictAtFast_sound (row 17 45) 17 45 hvalid hfast

theorem strict_r17_part46 : ∀ i ∈ List.range 1, StrictCheckAt 17 (46+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 46 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 46) 17 46 := by decide +kernel
  exact strictAtFast_sound (row 17 46) 17 46 hvalid hfast

theorem strict_r17_part47 : ∀ i ∈ List.range 1, StrictCheckAt 17 (47+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 17 47 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 17 47) 17 47 := by decide +kernel
  exact strictAtFast_sound (row 17 47) 17 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
