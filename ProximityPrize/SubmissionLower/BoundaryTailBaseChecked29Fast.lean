import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r29_part0 : ∀ i ∈ List.range 8, CorrectAt 29 (0+i) := by
  decide +kernel

theorem base_r29_part0 : ∀ i ∈ List.range 8, BaseCheckAt 29 (0+i) := by
  decide +kernel

theorem strict_r29_part0 : ∀ i ∈ List.range 8, StrictCheckAt 29 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (0+i)) 29 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (0+i)) 29 (0+i)
    (validAll 29 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part1 : ∀ i ∈ List.range 8, CorrectAt 29 (8+i) := by
  decide +kernel

theorem base_r29_part1 : ∀ i ∈ List.range 8, BaseCheckAt 29 (8+i) := by
  decide +kernel

theorem strict_r29_part1 : ∀ i ∈ List.range 8, StrictCheckAt 29 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (8+i)) 29 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (8+i)) 29 (8+i)
    (validAll 29 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part2 : ∀ i ∈ List.range 8, CorrectAt 29 (16+i) := by
  decide +kernel

theorem base_r29_part2 : ∀ i ∈ List.range 8, BaseCheckAt 29 (16+i) := by
  decide +kernel

theorem strict_r29_part2 : ∀ i ∈ List.range 8, StrictCheckAt 29 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (16+i)) 29 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (16+i)) 29 (16+i)
    (validAll 29 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part3 : ∀ i ∈ List.range 8, CorrectAt 29 (24+i) := by
  decide +kernel

theorem base_r29_part3 : ∀ i ∈ List.range 8, BaseCheckAt 29 (24+i) := by
  decide +kernel

theorem strict_r29_part3 : ∀ i ∈ List.range 8, StrictCheckAt 29 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (24+i)) 29 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (24+i)) 29 (24+i)
    (validAll 29 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part4 : ∀ i ∈ List.range 8, CorrectAt 29 (32+i) := by
  decide +kernel

theorem base_r29_part4 : ∀ i ∈ List.range 8, BaseCheckAt 29 (32+i) := by
  decide +kernel

theorem strict_r29_part4 : ∀ i ∈ List.range 8, StrictCheckAt 29 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (32+i)) 29 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (32+i)) 29 (32+i)
    (validAll 29 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part5 : ∀ i ∈ List.range 8, CorrectAt 29 (40+i) := by
  decide +kernel

theorem base_r29_part5 : ∀ i ∈ List.range 8, BaseCheckAt 29 (40+i) := by
  decide +kernel

theorem strict_r29_part5 : ∀ i ∈ List.range 8, StrictCheckAt 29 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (40+i)) 29 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (40+i)) 29 (40+i)
    (validAll 29 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part6 : ∀ i ∈ List.range 8, CorrectAt 29 (48+i) := by
  decide +kernel

theorem base_r29_part6 : ∀ i ∈ List.range 8, BaseCheckAt 29 (48+i) := by
  decide +kernel

theorem strict_r29_part6 : ∀ i ∈ List.range 8, StrictCheckAt 29 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (48+i)) 29 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (48+i)) 29 (48+i)
    (validAll 29 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part7 : ∀ i ∈ List.range 8, CorrectAt 29 (56+i) := by
  decide +kernel

theorem base_r29_part7 : ∀ i ∈ List.range 8, BaseCheckAt 29 (56+i) := by
  decide +kernel

theorem strict_r29_part7 : ∀ i ∈ List.range 8, StrictCheckAt 29 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (56+i)) 29 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (56+i)) 29 (56+i)
    (validAll 29 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part8 : ∀ i ∈ List.range 8, CorrectAt 29 (64+i) := by
  decide +kernel

theorem base_r29_part8 : ∀ i ∈ List.range 8, BaseCheckAt 29 (64+i) := by
  decide +kernel

theorem strict_r29_part8 : ∀ i ∈ List.range 8, StrictCheckAt 29 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (64+i)) 29 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (64+i)) 29 (64+i)
    (validAll 29 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part9 : ∀ i ∈ List.range 8, CorrectAt 29 (72+i) := by
  decide +kernel

theorem base_r29_part9 : ∀ i ∈ List.range 8, BaseCheckAt 29 (72+i) := by
  decide +kernel

theorem strict_r29_part9 : ∀ i ∈ List.range 8, StrictCheckAt 29 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (72+i)) 29 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (72+i)) 29 (72+i)
    (validAll 29 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part10 : ∀ i ∈ List.range 8, CorrectAt 29 (80+i) := by
  decide +kernel

theorem base_r29_part10 : ∀ i ∈ List.range 8, BaseCheckAt 29 (80+i) := by
  decide +kernel

theorem strict_r29_part10 : ∀ i ∈ List.range 8, StrictCheckAt 29 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (80+i)) 29 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (80+i)) 29 (80+i)
    (validAll 29 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part11 : ∀ i ∈ List.range 8, CorrectAt 29 (88+i) := by
  decide +kernel

theorem base_r29_part11 : ∀ i ∈ List.range 8, BaseCheckAt 29 (88+i) := by
  decide +kernel

theorem strict_r29_part11 : ∀ i ∈ List.range 8, StrictCheckAt 29 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (88+i)) 29 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (88+i)) 29 (88+i)
    (validAll 29 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part12 : ∀ i ∈ List.range 8, CorrectAt 29 (96+i) := by
  decide +kernel

theorem base_r29_part12 : ∀ i ∈ List.range 8, BaseCheckAt 29 (96+i) := by
  decide +kernel

theorem strict_r29_part12 : ∀ i ∈ List.range 8, StrictCheckAt 29 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 29 (96+i)) 29 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (96+i)) 29 (96+i)
    (validAll 29 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r29_part13 : ∀ i ∈ List.range 7, CorrectAt 29 (104+i) := by
  decide +kernel

theorem base_r29_part13 : ∀ i ∈ List.range 7, BaseCheckAt 29 (104+i) := by
  decide +kernel

theorem strict_r29_part13 : ∀ i ∈ List.range 7, StrictCheckAt 29 (104+i) := by
  have hfast : ∀ i ∈ List.range 7, StrictAtFast (row 29 (104+i)) 29 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 7 := List.mem_range.mp hi
  exact strictAtFast_sound (row 29 (104+i)) 29 (104+i)
    (validAll 29 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
