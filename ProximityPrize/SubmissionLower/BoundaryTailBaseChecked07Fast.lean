import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked06
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastValidated

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r7_part0 : ∀ i ∈ List.range 8, CorrectAt 7 (0+i) := by
  decide +kernel

theorem base_r7_part0 : ∀ i ∈ List.range 8, BaseCheckAt 7 (0+i) := by
  decide +kernel

theorem strict_r7_part0 : ∀ i ∈ List.range 8, StrictCheckAt 7 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (0+i)) 7 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (0+i)) 7 (0+i)
    (validAll 7 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part1 : ∀ i ∈ List.range 8, CorrectAt 7 (8+i) := by
  decide +kernel

theorem base_r7_part1 : ∀ i ∈ List.range 8, BaseCheckAt 7 (8+i) := by
  decide +kernel

theorem strict_r7_part1 : ∀ i ∈ List.range 8, StrictCheckAt 7 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (8+i)) 7 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (8+i)) 7 (8+i)
    (validAll 7 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part2 : ∀ i ∈ List.range 8, CorrectAt 7 (16+i) := by
  decide +kernel

theorem base_r7_part2 : ∀ i ∈ List.range 8, BaseCheckAt 7 (16+i) := by
  decide +kernel

theorem strict_r7_part2 : ∀ i ∈ List.range 8, StrictCheckAt 7 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (16+i)) 7 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (16+i)) 7 (16+i)
    (validAll 7 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part3 : ∀ i ∈ List.range 8, CorrectAt 7 (24+i) := by
  decide +kernel

theorem base_r7_part3 : ∀ i ∈ List.range 8, BaseCheckAt 7 (24+i) := by
  decide +kernel

theorem strict_r7_part3 : ∀ i ∈ List.range 8, StrictCheckAt 7 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (24+i)) 7 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (24+i)) 7 (24+i)
    (validAll 7 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part4 : ∀ i ∈ List.range 8, CorrectAt 7 (32+i) := by
  decide +kernel

theorem base_r7_part4 : ∀ i ∈ List.range 8, BaseCheckAt 7 (32+i) := by
  decide +kernel

theorem strict_r7_part4 : ∀ i ∈ List.range 8, StrictCheckAt 7 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (32+i)) 7 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (32+i)) 7 (32+i)
    (validAll 7 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part5 : ∀ i ∈ List.range 8, CorrectAt 7 (40+i) := by
  decide +kernel

theorem base_r7_part5 : ∀ i ∈ List.range 8, BaseCheckAt 7 (40+i) := by
  decide +kernel

theorem strict_r7_part5 : ∀ i ∈ List.range 8, StrictCheckAt 7 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (40+i)) 7 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (40+i)) 7 (40+i)
    (validAll 7 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part6 : ∀ i ∈ List.range 8, CorrectAt 7 (48+i) := by
  decide +kernel

theorem base_r7_part6 : ∀ i ∈ List.range 8, BaseCheckAt 7 (48+i) := by
  decide +kernel

theorem strict_r7_part6 : ∀ i ∈ List.range 8, StrictCheckAt 7 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (48+i)) 7 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (48+i)) 7 (48+i)
    (validAll 7 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part7 : ∀ i ∈ List.range 8, CorrectAt 7 (56+i) := by
  decide +kernel

theorem base_r7_part7 : ∀ i ∈ List.range 8, BaseCheckAt 7 (56+i) := by
  decide +kernel

theorem strict_r7_part7 : ∀ i ∈ List.range 8, StrictCheckAt 7 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (56+i)) 7 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (56+i)) 7 (56+i)
    (validAll 7 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part8 : ∀ i ∈ List.range 8, CorrectAt 7 (64+i) := by
  decide +kernel

theorem base_r7_part8 : ∀ i ∈ List.range 8, BaseCheckAt 7 (64+i) := by
  decide +kernel

theorem strict_r7_part8 : ∀ i ∈ List.range 8, StrictCheckAt 7 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (64+i)) 7 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (64+i)) 7 (64+i)
    (validAll 7 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part9 : ∀ i ∈ List.range 8, CorrectAt 7 (72+i) := by
  decide +kernel

theorem base_r7_part9 : ∀ i ∈ List.range 8, BaseCheckAt 7 (72+i) := by
  decide +kernel

theorem strict_r7_part9 : ∀ i ∈ List.range 8, StrictCheckAt 7 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (72+i)) 7 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (72+i)) 7 (72+i)
    (validAll 7 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part10 : ∀ i ∈ List.range 8, CorrectAt 7 (80+i) := by
  decide +kernel

theorem base_r7_part10 : ∀ i ∈ List.range 8, BaseCheckAt 7 (80+i) := by
  decide +kernel

theorem strict_r7_part10 : ∀ i ∈ List.range 8, StrictCheckAt 7 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (80+i)) 7 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (80+i)) 7 (80+i)
    (validAll 7 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part11 : ∀ i ∈ List.range 8, CorrectAt 7 (88+i) := by
  decide +kernel

theorem base_r7_part11 : ∀ i ∈ List.range 8, BaseCheckAt 7 (88+i) := by
  decide +kernel

theorem strict_r7_part11 : ∀ i ∈ List.range 8, StrictCheckAt 7 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (88+i)) 7 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (88+i)) 7 (88+i)
    (validAll 7 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part12 : ∀ i ∈ List.range 8, CorrectAt 7 (96+i) := by
  decide +kernel

theorem base_r7_part12 : ∀ i ∈ List.range 8, BaseCheckAt 7 (96+i) := by
  decide +kernel

theorem strict_r7_part12 : ∀ i ∈ List.range 8, StrictCheckAt 7 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (96+i)) 7 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (96+i)) 7 (96+i)
    (validAll 7 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part13 : ∀ i ∈ List.range 8, CorrectAt 7 (104+i) := by
  decide +kernel

theorem base_r7_part13 : ∀ i ∈ List.range 8, BaseCheckAt 7 (104+i) := by
  decide +kernel

theorem strict_r7_part13 : ∀ i ∈ List.range 8, StrictCheckAt 7 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (104+i)) 7 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (104+i)) 7 (104+i)
    (validAll 7 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part14 : ∀ i ∈ List.range 8, CorrectAt 7 (112+i) := by
  decide +kernel

theorem base_r7_part14 : ∀ i ∈ List.range 8, BaseCheckAt 7 (112+i) := by
  decide +kernel

theorem strict_r7_part14 : ∀ i ∈ List.range 8, StrictCheckAt 7 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (112+i)) 7 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (112+i)) 7 (112+i)
    (validAll 7 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part15 : ∀ i ∈ List.range 8, CorrectAt 7 (120+i) := by
  decide +kernel

theorem base_r7_part15 : ∀ i ∈ List.range 8, BaseCheckAt 7 (120+i) := by
  decide +kernel

theorem strict_r7_part15 : ∀ i ∈ List.range 8, StrictCheckAt 7 (120+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 7 (120+i)) 7 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (120+i)) 7 (120+i)
    (validAll 7 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r7_part16 : ∀ i ∈ List.range 5, CorrectAt 7 (128+i) := by
  decide +kernel

theorem base_r7_part16 : ∀ i ∈ List.range 5, BaseCheckAt 7 (128+i) := by
  decide +kernel

theorem strict_r7_part16 : ∀ i ∈ List.range 5, StrictCheckAt 7 (128+i) := by
  have hfast : ∀ i ∈ List.range 5, StrictAtFast (row 7 (128+i)) 7 (128+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 5 := List.mem_range.mp hi
  exact strictAtFast_sound (row 7 (128+i)) 7 (128+i)
    (validAll 7 (128+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
