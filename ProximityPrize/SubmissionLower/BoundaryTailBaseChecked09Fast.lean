import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r9_part0 : ∀ i ∈ List.range 8, CorrectAt 9 (0+i) := by
  decide +kernel

theorem base_r9_part0 : ∀ i ∈ List.range 8, BaseCheckAt 9 (0+i) := by
  decide +kernel

theorem strict_r9_part0 : ∀ i ∈ List.range 8, StrictCheckAt 9 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (0+i)) 9 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (0+i)) 9 (0+i)
    (validAll 9 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part1 : ∀ i ∈ List.range 8, CorrectAt 9 (8+i) := by
  decide +kernel

theorem base_r9_part1 : ∀ i ∈ List.range 8, BaseCheckAt 9 (8+i) := by
  decide +kernel

theorem strict_r9_part1 : ∀ i ∈ List.range 8, StrictCheckAt 9 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (8+i)) 9 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (8+i)) 9 (8+i)
    (validAll 9 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part2 : ∀ i ∈ List.range 8, CorrectAt 9 (16+i) := by
  decide +kernel

theorem base_r9_part2 : ∀ i ∈ List.range 8, BaseCheckAt 9 (16+i) := by
  decide +kernel

theorem strict_r9_part2 : ∀ i ∈ List.range 8, StrictCheckAt 9 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (16+i)) 9 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (16+i)) 9 (16+i)
    (validAll 9 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part3 : ∀ i ∈ List.range 8, CorrectAt 9 (24+i) := by
  decide +kernel

theorem base_r9_part3 : ∀ i ∈ List.range 8, BaseCheckAt 9 (24+i) := by
  decide +kernel

theorem strict_r9_part3 : ∀ i ∈ List.range 8, StrictCheckAt 9 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (24+i)) 9 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (24+i)) 9 (24+i)
    (validAll 9 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part4 : ∀ i ∈ List.range 8, CorrectAt 9 (32+i) := by
  decide +kernel

theorem base_r9_part4 : ∀ i ∈ List.range 8, BaseCheckAt 9 (32+i) := by
  decide +kernel

theorem strict_r9_part4 : ∀ i ∈ List.range 8, StrictCheckAt 9 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (32+i)) 9 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (32+i)) 9 (32+i)
    (validAll 9 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part5 : ∀ i ∈ List.range 8, CorrectAt 9 (40+i) := by
  decide +kernel

theorem base_r9_part5 : ∀ i ∈ List.range 8, BaseCheckAt 9 (40+i) := by
  decide +kernel

theorem strict_r9_part5 : ∀ i ∈ List.range 8, StrictCheckAt 9 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (40+i)) 9 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (40+i)) 9 (40+i)
    (validAll 9 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part6 : ∀ i ∈ List.range 8, CorrectAt 9 (48+i) := by
  decide +kernel

theorem base_r9_part6 : ∀ i ∈ List.range 8, BaseCheckAt 9 (48+i) := by
  decide +kernel

theorem strict_r9_part6 : ∀ i ∈ List.range 8, StrictCheckAt 9 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (48+i)) 9 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (48+i)) 9 (48+i)
    (validAll 9 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part7 : ∀ i ∈ List.range 8, CorrectAt 9 (56+i) := by
  decide +kernel

theorem base_r9_part7 : ∀ i ∈ List.range 8, BaseCheckAt 9 (56+i) := by
  decide +kernel

theorem strict_r9_part7 : ∀ i ∈ List.range 8, StrictCheckAt 9 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (56+i)) 9 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (56+i)) 9 (56+i)
    (validAll 9 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part8 : ∀ i ∈ List.range 8, CorrectAt 9 (64+i) := by
  decide +kernel

theorem base_r9_part8 : ∀ i ∈ List.range 8, BaseCheckAt 9 (64+i) := by
  decide +kernel

theorem strict_r9_part8 : ∀ i ∈ List.range 8, StrictCheckAt 9 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (64+i)) 9 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (64+i)) 9 (64+i)
    (validAll 9 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part9 : ∀ i ∈ List.range 8, CorrectAt 9 (72+i) := by
  decide +kernel

theorem base_r9_part9 : ∀ i ∈ List.range 8, BaseCheckAt 9 (72+i) := by
  decide +kernel

theorem strict_r9_part9 : ∀ i ∈ List.range 8, StrictCheckAt 9 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (72+i)) 9 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (72+i)) 9 (72+i)
    (validAll 9 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part10 : ∀ i ∈ List.range 8, CorrectAt 9 (80+i) := by
  decide +kernel

theorem base_r9_part10 : ∀ i ∈ List.range 8, BaseCheckAt 9 (80+i) := by
  decide +kernel

theorem strict_r9_part10 : ∀ i ∈ List.range 8, StrictCheckAt 9 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (80+i)) 9 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (80+i)) 9 (80+i)
    (validAll 9 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part11 : ∀ i ∈ List.range 8, CorrectAt 9 (88+i) := by
  decide +kernel

theorem base_r9_part11 : ∀ i ∈ List.range 8, BaseCheckAt 9 (88+i) := by
  decide +kernel

theorem strict_r9_part11 : ∀ i ∈ List.range 8, StrictCheckAt 9 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (88+i)) 9 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (88+i)) 9 (88+i)
    (validAll 9 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part12 : ∀ i ∈ List.range 8, CorrectAt 9 (96+i) := by
  decide +kernel

theorem base_r9_part12 : ∀ i ∈ List.range 8, BaseCheckAt 9 (96+i) := by
  decide +kernel

theorem strict_r9_part12 : ∀ i ∈ List.range 8, StrictCheckAt 9 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (96+i)) 9 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (96+i)) 9 (96+i)
    (validAll 9 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part13 : ∀ i ∈ List.range 8, CorrectAt 9 (104+i) := by
  decide +kernel

theorem base_r9_part13 : ∀ i ∈ List.range 8, BaseCheckAt 9 (104+i) := by
  decide +kernel

theorem strict_r9_part13 : ∀ i ∈ List.range 8, StrictCheckAt 9 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (104+i)) 9 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (104+i)) 9 (104+i)
    (validAll 9 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part14 : ∀ i ∈ List.range 8, CorrectAt 9 (112+i) := by
  decide +kernel

theorem base_r9_part14 : ∀ i ∈ List.range 8, BaseCheckAt 9 (112+i) := by
  decide +kernel

theorem strict_r9_part14 : ∀ i ∈ List.range 8, StrictCheckAt 9 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (112+i)) 9 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (112+i)) 9 (112+i)
    (validAll 9 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part15 : ∀ i ∈ List.range 8, CorrectAt 9 (120+i) := by
  decide +kernel

theorem base_r9_part15 : ∀ i ∈ List.range 8, BaseCheckAt 9 (120+i) := by
  decide +kernel

theorem strict_r9_part15 : ∀ i ∈ List.range 8, StrictCheckAt 9 (120+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 9 (120+i)) 9 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (120+i)) 9 (120+i)
    (validAll 9 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r9_part16 : ∀ i ∈ List.range 3, CorrectAt 9 (128+i) := by
  decide +kernel

theorem base_r9_part16 : ∀ i ∈ List.range 3, BaseCheckAt 9 (128+i) := by
  decide +kernel

theorem strict_r9_part16 : ∀ i ∈ List.range 3, StrictCheckAt 9 (128+i) := by
  have hfast : ∀ i ∈ List.range 3, StrictAtFast (row 9 (128+i)) 9 (128+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 3 := List.mem_range.mp hi
  exact strictAtFast_sound (row 9 (128+i)) 9 (128+i)
    (validAll 9 (128+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
