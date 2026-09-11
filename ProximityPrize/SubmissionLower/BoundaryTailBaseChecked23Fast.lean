import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r23_part0 : ∀ i ∈ List.range 8, CorrectAt 23 (0+i) := by
  decide +kernel

theorem base_r23_part0 : ∀ i ∈ List.range 8, BaseCheckAt 23 (0+i) := by
  decide +kernel

theorem strict_r23_part0 : ∀ i ∈ List.range 8, StrictCheckAt 23 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (0+i)) 23 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (0+i)) 23 (0+i)
    (validAll 23 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part1 : ∀ i ∈ List.range 8, CorrectAt 23 (8+i) := by
  decide +kernel

theorem base_r23_part1 : ∀ i ∈ List.range 8, BaseCheckAt 23 (8+i) := by
  decide +kernel

theorem strict_r23_part1 : ∀ i ∈ List.range 8, StrictCheckAt 23 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (8+i)) 23 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (8+i)) 23 (8+i)
    (validAll 23 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part2 : ∀ i ∈ List.range 8, CorrectAt 23 (16+i) := by
  decide +kernel

theorem base_r23_part2 : ∀ i ∈ List.range 8, BaseCheckAt 23 (16+i) := by
  decide +kernel

theorem strict_r23_part2 : ∀ i ∈ List.range 8, StrictCheckAt 23 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (16+i)) 23 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (16+i)) 23 (16+i)
    (validAll 23 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part3 : ∀ i ∈ List.range 8, CorrectAt 23 (24+i) := by
  decide +kernel

theorem base_r23_part3 : ∀ i ∈ List.range 8, BaseCheckAt 23 (24+i) := by
  decide +kernel

theorem strict_r23_part3 : ∀ i ∈ List.range 8, StrictCheckAt 23 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (24+i)) 23 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (24+i)) 23 (24+i)
    (validAll 23 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part4 : ∀ i ∈ List.range 8, CorrectAt 23 (32+i) := by
  decide +kernel

theorem base_r23_part4 : ∀ i ∈ List.range 8, BaseCheckAt 23 (32+i) := by
  decide +kernel

theorem strict_r23_part4 : ∀ i ∈ List.range 8, StrictCheckAt 23 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (32+i)) 23 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (32+i)) 23 (32+i)
    (validAll 23 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part5 : ∀ i ∈ List.range 8, CorrectAt 23 (40+i) := by
  decide +kernel

theorem base_r23_part5 : ∀ i ∈ List.range 8, BaseCheckAt 23 (40+i) := by
  decide +kernel

theorem strict_r23_part5 : ∀ i ∈ List.range 8, StrictCheckAt 23 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (40+i)) 23 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (40+i)) 23 (40+i)
    (validAll 23 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part6 : ∀ i ∈ List.range 8, CorrectAt 23 (48+i) := by
  decide +kernel

theorem base_r23_part6 : ∀ i ∈ List.range 8, BaseCheckAt 23 (48+i) := by
  decide +kernel

theorem strict_r23_part6 : ∀ i ∈ List.range 8, StrictCheckAt 23 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (48+i)) 23 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (48+i)) 23 (48+i)
    (validAll 23 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part7 : ∀ i ∈ List.range 8, CorrectAt 23 (56+i) := by
  decide +kernel

theorem base_r23_part7 : ∀ i ∈ List.range 8, BaseCheckAt 23 (56+i) := by
  decide +kernel

theorem strict_r23_part7 : ∀ i ∈ List.range 8, StrictCheckAt 23 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (56+i)) 23 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (56+i)) 23 (56+i)
    (validAll 23 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part8 : ∀ i ∈ List.range 8, CorrectAt 23 (64+i) := by
  decide +kernel

theorem base_r23_part8 : ∀ i ∈ List.range 8, BaseCheckAt 23 (64+i) := by
  decide +kernel

theorem strict_r23_part8 : ∀ i ∈ List.range 8, StrictCheckAt 23 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (64+i)) 23 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (64+i)) 23 (64+i)
    (validAll 23 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part9 : ∀ i ∈ List.range 8, CorrectAt 23 (72+i) := by
  decide +kernel

theorem base_r23_part9 : ∀ i ∈ List.range 8, BaseCheckAt 23 (72+i) := by
  decide +kernel

theorem strict_r23_part9 : ∀ i ∈ List.range 8, StrictCheckAt 23 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (72+i)) 23 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (72+i)) 23 (72+i)
    (validAll 23 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part10 : ∀ i ∈ List.range 8, CorrectAt 23 (80+i) := by
  decide +kernel

theorem base_r23_part10 : ∀ i ∈ List.range 8, BaseCheckAt 23 (80+i) := by
  decide +kernel

theorem strict_r23_part10 : ∀ i ∈ List.range 8, StrictCheckAt 23 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (80+i)) 23 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (80+i)) 23 (80+i)
    (validAll 23 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part11 : ∀ i ∈ List.range 8, CorrectAt 23 (88+i) := by
  decide +kernel

theorem base_r23_part11 : ∀ i ∈ List.range 8, BaseCheckAt 23 (88+i) := by
  decide +kernel

theorem strict_r23_part11 : ∀ i ∈ List.range 8, StrictCheckAt 23 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (88+i)) 23 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (88+i)) 23 (88+i)
    (validAll 23 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part12 : ∀ i ∈ List.range 8, CorrectAt 23 (96+i) := by
  decide +kernel

theorem base_r23_part12 : ∀ i ∈ List.range 8, BaseCheckAt 23 (96+i) := by
  decide +kernel

theorem strict_r23_part12 : ∀ i ∈ List.range 8, StrictCheckAt 23 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (96+i)) 23 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (96+i)) 23 (96+i)
    (validAll 23 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part13 : ∀ i ∈ List.range 8, CorrectAt 23 (104+i) := by
  decide +kernel

theorem base_r23_part13 : ∀ i ∈ List.range 8, BaseCheckAt 23 (104+i) := by
  decide +kernel

theorem strict_r23_part13 : ∀ i ∈ List.range 8, StrictCheckAt 23 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 23 (104+i)) 23 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (104+i)) 23 (104+i)
    (validAll 23 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r23_part14 : ∀ i ∈ List.range 5, CorrectAt 23 (112+i) := by
  decide +kernel

theorem base_r23_part14 : ∀ i ∈ List.range 5, BaseCheckAt 23 (112+i) := by
  decide +kernel

theorem strict_r23_part14 : ∀ i ∈ List.range 5, StrictCheckAt 23 (112+i) := by
  have hfast : ∀ i ∈ List.range 5, StrictAtFast (row 23 (112+i)) 23 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 5 := List.mem_range.mp hi
  exact strictAtFast_sound (row 23 (112+i)) 23 (112+i)
    (validAll 23 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
