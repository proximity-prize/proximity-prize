import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r30_part0 : ∀ i ∈ List.range 8, CorrectAt 30 (0+i) := by
  decide +kernel

theorem base_r30_part0 : ∀ i ∈ List.range 8, BaseCheckAt 30 (0+i) := by
  decide +kernel

theorem strict_r30_part0 : ∀ i ∈ List.range 8, StrictCheckAt 30 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (0+i)) 30 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (0+i)) 30 (0+i)
    (validAll 30 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part1 : ∀ i ∈ List.range 8, CorrectAt 30 (8+i) := by
  decide +kernel

theorem base_r30_part1 : ∀ i ∈ List.range 8, BaseCheckAt 30 (8+i) := by
  decide +kernel

theorem strict_r30_part1 : ∀ i ∈ List.range 8, StrictCheckAt 30 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (8+i)) 30 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (8+i)) 30 (8+i)
    (validAll 30 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part2 : ∀ i ∈ List.range 8, CorrectAt 30 (16+i) := by
  decide +kernel

theorem base_r30_part2 : ∀ i ∈ List.range 8, BaseCheckAt 30 (16+i) := by
  decide +kernel

theorem strict_r30_part2 : ∀ i ∈ List.range 8, StrictCheckAt 30 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (16+i)) 30 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (16+i)) 30 (16+i)
    (validAll 30 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part3 : ∀ i ∈ List.range 8, CorrectAt 30 (24+i) := by
  decide +kernel

theorem base_r30_part3 : ∀ i ∈ List.range 8, BaseCheckAt 30 (24+i) := by
  decide +kernel

theorem strict_r30_part3 : ∀ i ∈ List.range 8, StrictCheckAt 30 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (24+i)) 30 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (24+i)) 30 (24+i)
    (validAll 30 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part4 : ∀ i ∈ List.range 8, CorrectAt 30 (32+i) := by
  decide +kernel

theorem base_r30_part4 : ∀ i ∈ List.range 8, BaseCheckAt 30 (32+i) := by
  decide +kernel

theorem strict_r30_part4 : ∀ i ∈ List.range 8, StrictCheckAt 30 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (32+i)) 30 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (32+i)) 30 (32+i)
    (validAll 30 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part5 : ∀ i ∈ List.range 8, CorrectAt 30 (40+i) := by
  decide +kernel

theorem base_r30_part5 : ∀ i ∈ List.range 8, BaseCheckAt 30 (40+i) := by
  decide +kernel

theorem strict_r30_part5 : ∀ i ∈ List.range 8, StrictCheckAt 30 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (40+i)) 30 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (40+i)) 30 (40+i)
    (validAll 30 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part6 : ∀ i ∈ List.range 8, CorrectAt 30 (48+i) := by
  decide +kernel

theorem base_r30_part6 : ∀ i ∈ List.range 8, BaseCheckAt 30 (48+i) := by
  decide +kernel

theorem strict_r30_part6 : ∀ i ∈ List.range 8, StrictCheckAt 30 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (48+i)) 30 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (48+i)) 30 (48+i)
    (validAll 30 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part7 : ∀ i ∈ List.range 8, CorrectAt 30 (56+i) := by
  decide +kernel

theorem base_r30_part7 : ∀ i ∈ List.range 8, BaseCheckAt 30 (56+i) := by
  decide +kernel

theorem strict_r30_part7 : ∀ i ∈ List.range 8, StrictCheckAt 30 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (56+i)) 30 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (56+i)) 30 (56+i)
    (validAll 30 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part8 : ∀ i ∈ List.range 8, CorrectAt 30 (64+i) := by
  decide +kernel

theorem base_r30_part8 : ∀ i ∈ List.range 8, BaseCheckAt 30 (64+i) := by
  decide +kernel

theorem strict_r30_part8 : ∀ i ∈ List.range 8, StrictCheckAt 30 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (64+i)) 30 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (64+i)) 30 (64+i)
    (validAll 30 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part9 : ∀ i ∈ List.range 8, CorrectAt 30 (72+i) := by
  decide +kernel

theorem base_r30_part9 : ∀ i ∈ List.range 8, BaseCheckAt 30 (72+i) := by
  decide +kernel

theorem strict_r30_part9 : ∀ i ∈ List.range 8, StrictCheckAt 30 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (72+i)) 30 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (72+i)) 30 (72+i)
    (validAll 30 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part10 : ∀ i ∈ List.range 8, CorrectAt 30 (80+i) := by
  decide +kernel

theorem base_r30_part10 : ∀ i ∈ List.range 8, BaseCheckAt 30 (80+i) := by
  decide +kernel

theorem strict_r30_part10 : ∀ i ∈ List.range 8, StrictCheckAt 30 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (80+i)) 30 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (80+i)) 30 (80+i)
    (validAll 30 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part11 : ∀ i ∈ List.range 8, CorrectAt 30 (88+i) := by
  decide +kernel

theorem base_r30_part11 : ∀ i ∈ List.range 8, BaseCheckAt 30 (88+i) := by
  decide +kernel

theorem strict_r30_part11 : ∀ i ∈ List.range 8, StrictCheckAt 30 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (88+i)) 30 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (88+i)) 30 (88+i)
    (validAll 30 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part12 : ∀ i ∈ List.range 8, CorrectAt 30 (96+i) := by
  decide +kernel

theorem base_r30_part12 : ∀ i ∈ List.range 8, BaseCheckAt 30 (96+i) := by
  decide +kernel

theorem strict_r30_part12 : ∀ i ∈ List.range 8, StrictCheckAt 30 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 30 (96+i)) 30 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (96+i)) 30 (96+i)
    (validAll 30 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r30_part13 : ∀ i ∈ List.range 6, CorrectAt 30 (104+i) := by
  decide +kernel

theorem base_r30_part13 : ∀ i ∈ List.range 6, BaseCheckAt 30 (104+i) := by
  decide +kernel

theorem strict_r30_part13 : ∀ i ∈ List.range 6, StrictCheckAt 30 (104+i) := by
  have hfast : ∀ i ∈ List.range 6, StrictAtFast (row 30 (104+i)) 30 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 6 := List.mem_range.mp hi
  exact strictAtFast_sound (row 30 (104+i)) 30 (104+i)
    (validAll 30 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
