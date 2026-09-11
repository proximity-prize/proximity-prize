import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r28_part0 : ∀ i ∈ List.range 8, CorrectAt 28 (0+i) := by
  decide +kernel

theorem base_r28_part0 : ∀ i ∈ List.range 8, BaseCheckAt 28 (0+i) := by
  decide +kernel

theorem strict_r28_part0 : ∀ i ∈ List.range 8, StrictCheckAt 28 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (0+i)) 28 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (0+i)) 28 (0+i)
    (validAll 28 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part1 : ∀ i ∈ List.range 8, CorrectAt 28 (8+i) := by
  decide +kernel

theorem base_r28_part1 : ∀ i ∈ List.range 8, BaseCheckAt 28 (8+i) := by
  decide +kernel

theorem strict_r28_part1 : ∀ i ∈ List.range 8, StrictCheckAt 28 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (8+i)) 28 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (8+i)) 28 (8+i)
    (validAll 28 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part2 : ∀ i ∈ List.range 8, CorrectAt 28 (16+i) := by
  decide +kernel

theorem base_r28_part2 : ∀ i ∈ List.range 8, BaseCheckAt 28 (16+i) := by
  decide +kernel

theorem strict_r28_part2 : ∀ i ∈ List.range 8, StrictCheckAt 28 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (16+i)) 28 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (16+i)) 28 (16+i)
    (validAll 28 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part3 : ∀ i ∈ List.range 8, CorrectAt 28 (24+i) := by
  decide +kernel

theorem base_r28_part3 : ∀ i ∈ List.range 8, BaseCheckAt 28 (24+i) := by
  decide +kernel

theorem strict_r28_part3 : ∀ i ∈ List.range 8, StrictCheckAt 28 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (24+i)) 28 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (24+i)) 28 (24+i)
    (validAll 28 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part4 : ∀ i ∈ List.range 8, CorrectAt 28 (32+i) := by
  decide +kernel

theorem base_r28_part4 : ∀ i ∈ List.range 8, BaseCheckAt 28 (32+i) := by
  decide +kernel

theorem strict_r28_part4 : ∀ i ∈ List.range 8, StrictCheckAt 28 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (32+i)) 28 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (32+i)) 28 (32+i)
    (validAll 28 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part5 : ∀ i ∈ List.range 8, CorrectAt 28 (40+i) := by
  decide +kernel

theorem base_r28_part5 : ∀ i ∈ List.range 8, BaseCheckAt 28 (40+i) := by
  decide +kernel

theorem strict_r28_part5 : ∀ i ∈ List.range 8, StrictCheckAt 28 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (40+i)) 28 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (40+i)) 28 (40+i)
    (validAll 28 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part6 : ∀ i ∈ List.range 8, CorrectAt 28 (48+i) := by
  decide +kernel

theorem base_r28_part6 : ∀ i ∈ List.range 8, BaseCheckAt 28 (48+i) := by
  decide +kernel

theorem strict_r28_part6 : ∀ i ∈ List.range 8, StrictCheckAt 28 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (48+i)) 28 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (48+i)) 28 (48+i)
    (validAll 28 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part7 : ∀ i ∈ List.range 8, CorrectAt 28 (56+i) := by
  decide +kernel

theorem base_r28_part7 : ∀ i ∈ List.range 8, BaseCheckAt 28 (56+i) := by
  decide +kernel

theorem strict_r28_part7 : ∀ i ∈ List.range 8, StrictCheckAt 28 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (56+i)) 28 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (56+i)) 28 (56+i)
    (validAll 28 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part8 : ∀ i ∈ List.range 8, CorrectAt 28 (64+i) := by
  decide +kernel

theorem base_r28_part8 : ∀ i ∈ List.range 8, BaseCheckAt 28 (64+i) := by
  decide +kernel

theorem strict_r28_part8 : ∀ i ∈ List.range 8, StrictCheckAt 28 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (64+i)) 28 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (64+i)) 28 (64+i)
    (validAll 28 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part9 : ∀ i ∈ List.range 8, CorrectAt 28 (72+i) := by
  decide +kernel

theorem base_r28_part9 : ∀ i ∈ List.range 8, BaseCheckAt 28 (72+i) := by
  decide +kernel

theorem strict_r28_part9 : ∀ i ∈ List.range 8, StrictCheckAt 28 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (72+i)) 28 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (72+i)) 28 (72+i)
    (validAll 28 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part10 : ∀ i ∈ List.range 8, CorrectAt 28 (80+i) := by
  decide +kernel

theorem base_r28_part10 : ∀ i ∈ List.range 8, BaseCheckAt 28 (80+i) := by
  decide +kernel

theorem strict_r28_part10 : ∀ i ∈ List.range 8, StrictCheckAt 28 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (80+i)) 28 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (80+i)) 28 (80+i)
    (validAll 28 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part11 : ∀ i ∈ List.range 8, CorrectAt 28 (88+i) := by
  decide +kernel

theorem base_r28_part11 : ∀ i ∈ List.range 8, BaseCheckAt 28 (88+i) := by
  decide +kernel

theorem strict_r28_part11 : ∀ i ∈ List.range 8, StrictCheckAt 28 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (88+i)) 28 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (88+i)) 28 (88+i)
    (validAll 28 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part12 : ∀ i ∈ List.range 8, CorrectAt 28 (96+i) := by
  decide +kernel

theorem base_r28_part12 : ∀ i ∈ List.range 8, BaseCheckAt 28 (96+i) := by
  decide +kernel

theorem strict_r28_part12 : ∀ i ∈ List.range 8, StrictCheckAt 28 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (96+i)) 28 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (96+i)) 28 (96+i)
    (validAll 28 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r28_part13 : ∀ i ∈ List.range 8, CorrectAt 28 (104+i) := by
  decide +kernel

theorem base_r28_part13 : ∀ i ∈ List.range 8, BaseCheckAt 28 (104+i) := by
  decide +kernel

theorem strict_r28_part13 : ∀ i ∈ List.range 8, StrictCheckAt 28 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 28 (104+i)) 28 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 28 (104+i)) 28 (104+i)
    (validAll 28 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
