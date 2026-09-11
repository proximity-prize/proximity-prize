import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r11_part0 : ∀ i ∈ List.range 8, CorrectAt 11 (0+i) := by
  decide +kernel

theorem base_r11_part0 : ∀ i ∈ List.range 8, BaseCheckAt 11 (0+i) := by
  decide +kernel

theorem strict_r11_part0 : ∀ i ∈ List.range 8, StrictCheckAt 11 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (0+i)) 11 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (0+i)) 11 (0+i)
    (validAll 11 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part1 : ∀ i ∈ List.range 8, CorrectAt 11 (8+i) := by
  decide +kernel

theorem base_r11_part1 : ∀ i ∈ List.range 8, BaseCheckAt 11 (8+i) := by
  decide +kernel

theorem strict_r11_part1 : ∀ i ∈ List.range 8, StrictCheckAt 11 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (8+i)) 11 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (8+i)) 11 (8+i)
    (validAll 11 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part2 : ∀ i ∈ List.range 8, CorrectAt 11 (16+i) := by
  decide +kernel

theorem base_r11_part2 : ∀ i ∈ List.range 8, BaseCheckAt 11 (16+i) := by
  decide +kernel

theorem strict_r11_part2 : ∀ i ∈ List.range 8, StrictCheckAt 11 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (16+i)) 11 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (16+i)) 11 (16+i)
    (validAll 11 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part3 : ∀ i ∈ List.range 8, CorrectAt 11 (24+i) := by
  decide +kernel

theorem base_r11_part3 : ∀ i ∈ List.range 8, BaseCheckAt 11 (24+i) := by
  decide +kernel

theorem strict_r11_part3 : ∀ i ∈ List.range 8, StrictCheckAt 11 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (24+i)) 11 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (24+i)) 11 (24+i)
    (validAll 11 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part4 : ∀ i ∈ List.range 8, CorrectAt 11 (32+i) := by
  decide +kernel

theorem base_r11_part4 : ∀ i ∈ List.range 8, BaseCheckAt 11 (32+i) := by
  decide +kernel

theorem strict_r11_part4 : ∀ i ∈ List.range 8, StrictCheckAt 11 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (32+i)) 11 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (32+i)) 11 (32+i)
    (validAll 11 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part5 : ∀ i ∈ List.range 8, CorrectAt 11 (40+i) := by
  decide +kernel

theorem base_r11_part5 : ∀ i ∈ List.range 8, BaseCheckAt 11 (40+i) := by
  decide +kernel

theorem strict_r11_part5 : ∀ i ∈ List.range 8, StrictCheckAt 11 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (40+i)) 11 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (40+i)) 11 (40+i)
    (validAll 11 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part6 : ∀ i ∈ List.range 8, CorrectAt 11 (48+i) := by
  decide +kernel

theorem base_r11_part6 : ∀ i ∈ List.range 8, BaseCheckAt 11 (48+i) := by
  decide +kernel

theorem strict_r11_part6 : ∀ i ∈ List.range 8, StrictCheckAt 11 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (48+i)) 11 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (48+i)) 11 (48+i)
    (validAll 11 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part7 : ∀ i ∈ List.range 8, CorrectAt 11 (56+i) := by
  decide +kernel

theorem base_r11_part7 : ∀ i ∈ List.range 8, BaseCheckAt 11 (56+i) := by
  decide +kernel

theorem strict_r11_part7 : ∀ i ∈ List.range 8, StrictCheckAt 11 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (56+i)) 11 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (56+i)) 11 (56+i)
    (validAll 11 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part8 : ∀ i ∈ List.range 8, CorrectAt 11 (64+i) := by
  decide +kernel

theorem base_r11_part8 : ∀ i ∈ List.range 8, BaseCheckAt 11 (64+i) := by
  decide +kernel

theorem strict_r11_part8 : ∀ i ∈ List.range 8, StrictCheckAt 11 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (64+i)) 11 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (64+i)) 11 (64+i)
    (validAll 11 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part9 : ∀ i ∈ List.range 8, CorrectAt 11 (72+i) := by
  decide +kernel

theorem base_r11_part9 : ∀ i ∈ List.range 8, BaseCheckAt 11 (72+i) := by
  decide +kernel

theorem strict_r11_part9 : ∀ i ∈ List.range 8, StrictCheckAt 11 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (72+i)) 11 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (72+i)) 11 (72+i)
    (validAll 11 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part10 : ∀ i ∈ List.range 8, CorrectAt 11 (80+i) := by
  decide +kernel

theorem base_r11_part10 : ∀ i ∈ List.range 8, BaseCheckAt 11 (80+i) := by
  decide +kernel

theorem strict_r11_part10 : ∀ i ∈ List.range 8, StrictCheckAt 11 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (80+i)) 11 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (80+i)) 11 (80+i)
    (validAll 11 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part11 : ∀ i ∈ List.range 8, CorrectAt 11 (88+i) := by
  decide +kernel

theorem base_r11_part11 : ∀ i ∈ List.range 8, BaseCheckAt 11 (88+i) := by
  decide +kernel

theorem strict_r11_part11 : ∀ i ∈ List.range 8, StrictCheckAt 11 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (88+i)) 11 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (88+i)) 11 (88+i)
    (validAll 11 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part12 : ∀ i ∈ List.range 8, CorrectAt 11 (96+i) := by
  decide +kernel

theorem base_r11_part12 : ∀ i ∈ List.range 8, BaseCheckAt 11 (96+i) := by
  decide +kernel

theorem strict_r11_part12 : ∀ i ∈ List.range 8, StrictCheckAt 11 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (96+i)) 11 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (96+i)) 11 (96+i)
    (validAll 11 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part13 : ∀ i ∈ List.range 8, CorrectAt 11 (104+i) := by
  decide +kernel

theorem base_r11_part13 : ∀ i ∈ List.range 8, BaseCheckAt 11 (104+i) := by
  decide +kernel

theorem strict_r11_part13 : ∀ i ∈ List.range 8, StrictCheckAt 11 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (104+i)) 11 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (104+i)) 11 (104+i)
    (validAll 11 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part14 : ∀ i ∈ List.range 8, CorrectAt 11 (112+i) := by
  decide +kernel

theorem base_r11_part14 : ∀ i ∈ List.range 8, BaseCheckAt 11 (112+i) := by
  decide +kernel

theorem strict_r11_part14 : ∀ i ∈ List.range 8, StrictCheckAt 11 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (112+i)) 11 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (112+i)) 11 (112+i)
    (validAll 11 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part15 : ∀ i ∈ List.range 8, CorrectAt 11 (120+i) := by
  decide +kernel

theorem base_r11_part15 : ∀ i ∈ List.range 8, BaseCheckAt 11 (120+i) := by
  decide +kernel

theorem strict_r11_part15 : ∀ i ∈ List.range 8, StrictCheckAt 11 (120+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 11 (120+i)) 11 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (120+i)) 11 (120+i)
    (validAll 11 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r11_part16 : ∀ i ∈ List.range 1, CorrectAt 11 (128+i) := by
  decide +kernel

theorem base_r11_part16 : ∀ i ∈ List.range 1, BaseCheckAt 11 (128+i) := by
  decide +kernel

theorem strict_r11_part16 : ∀ i ∈ List.range 1, StrictCheckAt 11 (128+i) := by
  have hfast : ∀ i ∈ List.range 1, StrictAtFast (row 11 (128+i)) 11 (128+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 1 := List.mem_range.mp hi
  exact strictAtFast_sound (row 11 (128+i)) 11 (128+i)
    (validAll 11 (128+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
