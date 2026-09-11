import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r8_part0 : ∀ i ∈ List.range 8, CorrectAt 8 (0+i) := by
  decide +kernel

theorem base_r8_part0 : ∀ i ∈ List.range 8, BaseCheckAt 8 (0+i) := by
  decide +kernel

theorem strict_r8_part0 : ∀ i ∈ List.range 8, StrictCheckAt 8 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (0+i)) 8 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (0+i)) 8 (0+i)
    (validAll 8 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part1 : ∀ i ∈ List.range 8, CorrectAt 8 (8+i) := by
  decide +kernel

theorem base_r8_part1 : ∀ i ∈ List.range 8, BaseCheckAt 8 (8+i) := by
  decide +kernel

theorem strict_r8_part1 : ∀ i ∈ List.range 8, StrictCheckAt 8 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (8+i)) 8 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (8+i)) 8 (8+i)
    (validAll 8 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part2 : ∀ i ∈ List.range 8, CorrectAt 8 (16+i) := by
  decide +kernel

theorem base_r8_part2 : ∀ i ∈ List.range 8, BaseCheckAt 8 (16+i) := by
  decide +kernel

theorem strict_r8_part2 : ∀ i ∈ List.range 8, StrictCheckAt 8 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (16+i)) 8 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (16+i)) 8 (16+i)
    (validAll 8 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part3 : ∀ i ∈ List.range 8, CorrectAt 8 (24+i) := by
  decide +kernel

theorem base_r8_part3 : ∀ i ∈ List.range 8, BaseCheckAt 8 (24+i) := by
  decide +kernel

theorem strict_r8_part3 : ∀ i ∈ List.range 8, StrictCheckAt 8 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (24+i)) 8 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (24+i)) 8 (24+i)
    (validAll 8 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part4 : ∀ i ∈ List.range 8, CorrectAt 8 (32+i) := by
  decide +kernel

theorem base_r8_part4 : ∀ i ∈ List.range 8, BaseCheckAt 8 (32+i) := by
  decide +kernel

theorem strict_r8_part4 : ∀ i ∈ List.range 8, StrictCheckAt 8 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (32+i)) 8 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (32+i)) 8 (32+i)
    (validAll 8 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part5 : ∀ i ∈ List.range 8, CorrectAt 8 (40+i) := by
  decide +kernel

theorem base_r8_part5 : ∀ i ∈ List.range 8, BaseCheckAt 8 (40+i) := by
  decide +kernel

theorem strict_r8_part5 : ∀ i ∈ List.range 8, StrictCheckAt 8 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (40+i)) 8 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (40+i)) 8 (40+i)
    (validAll 8 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part6 : ∀ i ∈ List.range 8, CorrectAt 8 (48+i) := by
  decide +kernel

theorem base_r8_part6 : ∀ i ∈ List.range 8, BaseCheckAt 8 (48+i) := by
  decide +kernel

theorem strict_r8_part6 : ∀ i ∈ List.range 8, StrictCheckAt 8 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (48+i)) 8 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (48+i)) 8 (48+i)
    (validAll 8 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part7 : ∀ i ∈ List.range 8, CorrectAt 8 (56+i) := by
  decide +kernel

theorem base_r8_part7 : ∀ i ∈ List.range 8, BaseCheckAt 8 (56+i) := by
  decide +kernel

theorem strict_r8_part7 : ∀ i ∈ List.range 8, StrictCheckAt 8 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (56+i)) 8 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (56+i)) 8 (56+i)
    (validAll 8 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part8 : ∀ i ∈ List.range 8, CorrectAt 8 (64+i) := by
  decide +kernel

theorem base_r8_part8 : ∀ i ∈ List.range 8, BaseCheckAt 8 (64+i) := by
  decide +kernel

theorem strict_r8_part8 : ∀ i ∈ List.range 8, StrictCheckAt 8 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (64+i)) 8 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (64+i)) 8 (64+i)
    (validAll 8 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part9 : ∀ i ∈ List.range 8, CorrectAt 8 (72+i) := by
  decide +kernel

theorem base_r8_part9 : ∀ i ∈ List.range 8, BaseCheckAt 8 (72+i) := by
  decide +kernel

theorem strict_r8_part9 : ∀ i ∈ List.range 8, StrictCheckAt 8 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (72+i)) 8 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (72+i)) 8 (72+i)
    (validAll 8 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part10 : ∀ i ∈ List.range 8, CorrectAt 8 (80+i) := by
  decide +kernel

theorem base_r8_part10 : ∀ i ∈ List.range 8, BaseCheckAt 8 (80+i) := by
  decide +kernel

theorem strict_r8_part10 : ∀ i ∈ List.range 8, StrictCheckAt 8 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (80+i)) 8 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (80+i)) 8 (80+i)
    (validAll 8 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part11 : ∀ i ∈ List.range 8, CorrectAt 8 (88+i) := by
  decide +kernel

theorem base_r8_part11 : ∀ i ∈ List.range 8, BaseCheckAt 8 (88+i) := by
  decide +kernel

theorem strict_r8_part11 : ∀ i ∈ List.range 8, StrictCheckAt 8 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (88+i)) 8 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (88+i)) 8 (88+i)
    (validAll 8 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part12 : ∀ i ∈ List.range 8, CorrectAt 8 (96+i) := by
  decide +kernel

theorem base_r8_part12 : ∀ i ∈ List.range 8, BaseCheckAt 8 (96+i) := by
  decide +kernel

theorem strict_r8_part12 : ∀ i ∈ List.range 8, StrictCheckAt 8 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (96+i)) 8 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (96+i)) 8 (96+i)
    (validAll 8 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part13 : ∀ i ∈ List.range 8, CorrectAt 8 (104+i) := by
  decide +kernel

theorem base_r8_part13 : ∀ i ∈ List.range 8, BaseCheckAt 8 (104+i) := by
  decide +kernel

theorem strict_r8_part13 : ∀ i ∈ List.range 8, StrictCheckAt 8 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (104+i)) 8 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (104+i)) 8 (104+i)
    (validAll 8 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part14 : ∀ i ∈ List.range 8, CorrectAt 8 (112+i) := by
  decide +kernel

theorem base_r8_part14 : ∀ i ∈ List.range 8, BaseCheckAt 8 (112+i) := by
  decide +kernel

theorem strict_r8_part14 : ∀ i ∈ List.range 8, StrictCheckAt 8 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (112+i)) 8 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (112+i)) 8 (112+i)
    (validAll 8 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part15 : ∀ i ∈ List.range 8, CorrectAt 8 (120+i) := by
  decide +kernel

theorem base_r8_part15 : ∀ i ∈ List.range 8, BaseCheckAt 8 (120+i) := by
  decide +kernel

theorem strict_r8_part15 : ∀ i ∈ List.range 8, StrictCheckAt 8 (120+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 8 (120+i)) 8 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (120+i)) 8 (120+i)
    (validAll 8 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r8_part16 : ∀ i ∈ List.range 4, CorrectAt 8 (128+i) := by
  decide +kernel

theorem base_r8_part16 : ∀ i ∈ List.range 4, BaseCheckAt 8 (128+i) := by
  decide +kernel

theorem strict_r8_part16 : ∀ i ∈ List.range 4, StrictCheckAt 8 (128+i) := by
  have hfast : ∀ i ∈ List.range 4, StrictAtFast (row 8 (128+i)) 8 (128+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 4 := List.mem_range.mp hi
  exact strictAtFast_sound (row 8 (128+i)) 8 (128+i)
    (validAll 8 (128+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
