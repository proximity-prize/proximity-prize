import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r16_part0 : ∀ i ∈ List.range 8, CorrectAt 16 (0+i) := by
  decide +kernel

theorem base_r16_part0 : ∀ i ∈ List.range 8, BaseCheckAt 16 (0+i) := by
  decide +kernel

theorem strict_r16_part0 : ∀ i ∈ List.range 8, StrictCheckAt 16 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (0+i)) 16 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (0+i)) 16 (0+i)
    (validAll 16 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part1 : ∀ i ∈ List.range 8, CorrectAt 16 (8+i) := by
  decide +kernel

theorem base_r16_part1 : ∀ i ∈ List.range 8, BaseCheckAt 16 (8+i) := by
  decide +kernel

theorem strict_r16_part1 : ∀ i ∈ List.range 8, StrictCheckAt 16 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (8+i)) 16 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (8+i)) 16 (8+i)
    (validAll 16 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part2 : ∀ i ∈ List.range 8, CorrectAt 16 (16+i) := by
  decide +kernel

theorem base_r16_part2 : ∀ i ∈ List.range 8, BaseCheckAt 16 (16+i) := by
  decide +kernel

theorem strict_r16_part2 : ∀ i ∈ List.range 8, StrictCheckAt 16 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (16+i)) 16 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (16+i)) 16 (16+i)
    (validAll 16 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part3 : ∀ i ∈ List.range 8, CorrectAt 16 (24+i) := by
  decide +kernel

theorem base_r16_part3 : ∀ i ∈ List.range 8, BaseCheckAt 16 (24+i) := by
  decide +kernel

theorem strict_r16_part3 : ∀ i ∈ List.range 8, StrictCheckAt 16 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (24+i)) 16 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (24+i)) 16 (24+i)
    (validAll 16 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part4 : ∀ i ∈ List.range 8, CorrectAt 16 (32+i) := by
  decide +kernel

theorem base_r16_part4 : ∀ i ∈ List.range 8, BaseCheckAt 16 (32+i) := by
  decide +kernel

theorem strict_r16_part4 : ∀ i ∈ List.range 8, StrictCheckAt 16 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (32+i)) 16 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (32+i)) 16 (32+i)
    (validAll 16 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part5 : ∀ i ∈ List.range 8, CorrectAt 16 (40+i) := by
  decide +kernel

theorem base_r16_part5 : ∀ i ∈ List.range 8, BaseCheckAt 16 (40+i) := by
  decide +kernel

theorem strict_r16_part5 : ∀ i ∈ List.range 8, StrictCheckAt 16 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (40+i)) 16 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (40+i)) 16 (40+i)
    (validAll 16 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part6 : ∀ i ∈ List.range 8, CorrectAt 16 (48+i) := by
  decide +kernel

theorem base_r16_part6 : ∀ i ∈ List.range 8, BaseCheckAt 16 (48+i) := by
  decide +kernel

theorem strict_r16_part6 : ∀ i ∈ List.range 8, StrictCheckAt 16 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (48+i)) 16 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (48+i)) 16 (48+i)
    (validAll 16 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part7 : ∀ i ∈ List.range 8, CorrectAt 16 (56+i) := by
  decide +kernel

theorem base_r16_part7 : ∀ i ∈ List.range 8, BaseCheckAt 16 (56+i) := by
  decide +kernel

theorem strict_r16_part7 : ∀ i ∈ List.range 8, StrictCheckAt 16 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (56+i)) 16 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (56+i)) 16 (56+i)
    (validAll 16 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part8 : ∀ i ∈ List.range 8, CorrectAt 16 (64+i) := by
  decide +kernel

theorem base_r16_part8 : ∀ i ∈ List.range 8, BaseCheckAt 16 (64+i) := by
  decide +kernel

theorem strict_r16_part8 : ∀ i ∈ List.range 8, StrictCheckAt 16 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (64+i)) 16 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (64+i)) 16 (64+i)
    (validAll 16 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part9 : ∀ i ∈ List.range 8, CorrectAt 16 (72+i) := by
  decide +kernel

theorem base_r16_part9 : ∀ i ∈ List.range 8, BaseCheckAt 16 (72+i) := by
  decide +kernel

theorem strict_r16_part9 : ∀ i ∈ List.range 8, StrictCheckAt 16 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (72+i)) 16 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (72+i)) 16 (72+i)
    (validAll 16 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part10 : ∀ i ∈ List.range 8, CorrectAt 16 (80+i) := by
  decide +kernel

theorem base_r16_part10 : ∀ i ∈ List.range 8, BaseCheckAt 16 (80+i) := by
  decide +kernel

theorem strict_r16_part10 : ∀ i ∈ List.range 8, StrictCheckAt 16 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (80+i)) 16 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (80+i)) 16 (80+i)
    (validAll 16 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part11 : ∀ i ∈ List.range 8, CorrectAt 16 (88+i) := by
  decide +kernel

theorem base_r16_part11 : ∀ i ∈ List.range 8, BaseCheckAt 16 (88+i) := by
  decide +kernel

theorem strict_r16_part11 : ∀ i ∈ List.range 8, StrictCheckAt 16 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (88+i)) 16 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (88+i)) 16 (88+i)
    (validAll 16 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part12 : ∀ i ∈ List.range 8, CorrectAt 16 (96+i) := by
  decide +kernel

theorem base_r16_part12 : ∀ i ∈ List.range 8, BaseCheckAt 16 (96+i) := by
  decide +kernel

theorem strict_r16_part12 : ∀ i ∈ List.range 8, StrictCheckAt 16 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (96+i)) 16 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (96+i)) 16 (96+i)
    (validAll 16 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part13 : ∀ i ∈ List.range 8, CorrectAt 16 (104+i) := by
  decide +kernel

theorem base_r16_part13 : ∀ i ∈ List.range 8, BaseCheckAt 16 (104+i) := by
  decide +kernel

theorem strict_r16_part13 : ∀ i ∈ List.range 8, StrictCheckAt 16 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (104+i)) 16 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (104+i)) 16 (104+i)
    (validAll 16 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part14 : ∀ i ∈ List.range 8, CorrectAt 16 (112+i) := by
  decide +kernel

theorem base_r16_part14 : ∀ i ∈ List.range 8, BaseCheckAt 16 (112+i) := by
  decide +kernel

theorem strict_r16_part14 : ∀ i ∈ List.range 8, StrictCheckAt 16 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 16 (112+i)) 16 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (112+i)) 16 (112+i)
    (validAll 16 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r16_part15 : ∀ i ∈ List.range 4, CorrectAt 16 (120+i) := by
  decide +kernel

theorem base_r16_part15 : ∀ i ∈ List.range 4, BaseCheckAt 16 (120+i) := by
  decide +kernel

theorem strict_r16_part15 : ∀ i ∈ List.range 4, StrictCheckAt 16 (120+i) := by
  have hfast : ∀ i ∈ List.range 4, StrictAtFast (row 16 (120+i)) 16 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 4 := List.mem_range.mp hi
  exact strictAtFast_sound (row 16 (120+i)) 16 (120+i)
    (validAll 16 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
