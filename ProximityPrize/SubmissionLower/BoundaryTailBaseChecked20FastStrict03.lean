import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem strict_r20_part32 : ∀ i ∈ List.range 1, StrictCheckAt 20 (32+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 32 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 32) 20 32 := by decide +kernel
  exact strictAtFast_sound (row 20 32) 20 32 hvalid hfast

theorem strict_r20_part33 : ∀ i ∈ List.range 1, StrictCheckAt 20 (33+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 33 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 33) 20 33 := by decide +kernel
  exact strictAtFast_sound (row 20 33) 20 33 hvalid hfast

theorem strict_r20_part34 : ∀ i ∈ List.range 1, StrictCheckAt 20 (34+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 34 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 34) 20 34 := by decide +kernel
  exact strictAtFast_sound (row 20 34) 20 34 hvalid hfast

theorem strict_r20_part35 : ∀ i ∈ List.range 1, StrictCheckAt 20 (35+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 35 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 35) 20 35 := by decide +kernel
  exact strictAtFast_sound (row 20 35) 20 35 hvalid hfast

theorem strict_r20_part36 : ∀ i ∈ List.range 1, StrictCheckAt 20 (36+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 36 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 36) 20 36 := by decide +kernel
  exact strictAtFast_sound (row 20 36) 20 36 hvalid hfast

theorem strict_r20_part37 : ∀ i ∈ List.range 1, StrictCheckAt 20 (37+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 37 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 37) 20 37 := by decide +kernel
  exact strictAtFast_sound (row 20 37) 20 37 hvalid hfast

theorem strict_r20_part38 : ∀ i ∈ List.range 1, StrictCheckAt 20 (38+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 38 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 38) 20 38 := by decide +kernel
  exact strictAtFast_sound (row 20 38) 20 38 hvalid hfast

theorem strict_r20_part39 : ∀ i ∈ List.range 1, StrictCheckAt 20 (39+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 39 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 39) 20 39 := by decide +kernel
  exact strictAtFast_sound (row 20 39) 20 39 hvalid hfast

theorem strict_r20_part40 : ∀ i ∈ List.range 1, StrictCheckAt 20 (40+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 40 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 40) 20 40 := by decide +kernel
  exact strictAtFast_sound (row 20 40) 20 40 hvalid hfast

theorem strict_r20_part41 : ∀ i ∈ List.range 1, StrictCheckAt 20 (41+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 41 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 41) 20 41 := by decide +kernel
  exact strictAtFast_sound (row 20 41) 20 41 hvalid hfast

theorem strict_r20_part42 : ∀ i ∈ List.range 1, StrictCheckAt 20 (42+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 42 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 42) 20 42 := by decide +kernel
  exact strictAtFast_sound (row 20 42) 20 42 hvalid hfast

theorem strict_r20_part43 : ∀ i ∈ List.range 1, StrictCheckAt 20 (43+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 43 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 43) 20 43 := by decide +kernel
  exact strictAtFast_sound (row 20 43) 20 43 hvalid hfast

theorem strict_r20_part44 : ∀ i ∈ List.range 1, StrictCheckAt 20 (44+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 44 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 44) 20 44 := by decide +kernel
  exact strictAtFast_sound (row 20 44) 20 44 hvalid hfast

theorem strict_r20_part45 : ∀ i ∈ List.range 1, StrictCheckAt 20 (45+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 45 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 45) 20 45 := by decide +kernel
  exact strictAtFast_sound (row 20 45) 20 45 hvalid hfast

theorem strict_r20_part46 : ∀ i ∈ List.range 1, StrictCheckAt 20 (46+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 46 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 46) 20 46 := by decide +kernel
  exact strictAtFast_sound (row 20 46) 20 46 hvalid hfast

theorem strict_r20_part47 : ∀ i ∈ List.range 1, StrictCheckAt 20 (47+i) := by
  intro i hi
  have hi0 : i = 0 := by have := List.mem_range.mp hi; omega
  subst i
  simp only [Nat.add_zero]
  have hvalid := validAll 20 47 (by omega) (by omega) (by omega)
  have hfast : StrictAtFast (row 20 47) 20 47 := by decide +kernel
  exact strictAtFast_sound (row 20 47) 20 47 hvalid hfast

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
