import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r15_part0 : ∀ i ∈ List.range 8, CorrectAt 15 (0+i) := by
  decide +kernel

theorem base_r15_part0 : ∀ i ∈ List.range 8, BaseCheckAt 15 (0+i) := by
  decide +kernel

theorem strict_r15_part0 : ∀ i ∈ List.range 8, StrictCheckAt 15 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (0+i)) 15 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (0+i)) 15 (0+i)
    (validAll 15 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part1 : ∀ i ∈ List.range 8, CorrectAt 15 (8+i) := by
  decide +kernel

theorem base_r15_part1 : ∀ i ∈ List.range 8, BaseCheckAt 15 (8+i) := by
  decide +kernel

theorem strict_r15_part1 : ∀ i ∈ List.range 8, StrictCheckAt 15 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (8+i)) 15 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (8+i)) 15 (8+i)
    (validAll 15 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part2 : ∀ i ∈ List.range 8, CorrectAt 15 (16+i) := by
  decide +kernel

theorem base_r15_part2 : ∀ i ∈ List.range 8, BaseCheckAt 15 (16+i) := by
  decide +kernel

theorem strict_r15_part2 : ∀ i ∈ List.range 8, StrictCheckAt 15 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (16+i)) 15 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (16+i)) 15 (16+i)
    (validAll 15 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part3 : ∀ i ∈ List.range 8, CorrectAt 15 (24+i) := by
  decide +kernel

theorem base_r15_part3 : ∀ i ∈ List.range 8, BaseCheckAt 15 (24+i) := by
  decide +kernel

theorem strict_r15_part3 : ∀ i ∈ List.range 8, StrictCheckAt 15 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (24+i)) 15 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (24+i)) 15 (24+i)
    (validAll 15 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part4 : ∀ i ∈ List.range 8, CorrectAt 15 (32+i) := by
  decide +kernel

theorem base_r15_part4 : ∀ i ∈ List.range 8, BaseCheckAt 15 (32+i) := by
  decide +kernel

theorem strict_r15_part4 : ∀ i ∈ List.range 8, StrictCheckAt 15 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (32+i)) 15 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (32+i)) 15 (32+i)
    (validAll 15 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part5 : ∀ i ∈ List.range 8, CorrectAt 15 (40+i) := by
  decide +kernel

theorem base_r15_part5 : ∀ i ∈ List.range 8, BaseCheckAt 15 (40+i) := by
  decide +kernel

theorem strict_r15_part5 : ∀ i ∈ List.range 8, StrictCheckAt 15 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (40+i)) 15 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (40+i)) 15 (40+i)
    (validAll 15 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part6 : ∀ i ∈ List.range 8, CorrectAt 15 (48+i) := by
  decide +kernel

theorem base_r15_part6 : ∀ i ∈ List.range 8, BaseCheckAt 15 (48+i) := by
  decide +kernel

theorem strict_r15_part6 : ∀ i ∈ List.range 8, StrictCheckAt 15 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (48+i)) 15 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (48+i)) 15 (48+i)
    (validAll 15 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part7 : ∀ i ∈ List.range 8, CorrectAt 15 (56+i) := by
  decide +kernel

theorem base_r15_part7 : ∀ i ∈ List.range 8, BaseCheckAt 15 (56+i) := by
  decide +kernel

theorem strict_r15_part7 : ∀ i ∈ List.range 8, StrictCheckAt 15 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (56+i)) 15 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (56+i)) 15 (56+i)
    (validAll 15 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part8 : ∀ i ∈ List.range 8, CorrectAt 15 (64+i) := by
  decide +kernel

theorem base_r15_part8 : ∀ i ∈ List.range 8, BaseCheckAt 15 (64+i) := by
  decide +kernel

theorem strict_r15_part8 : ∀ i ∈ List.range 8, StrictCheckAt 15 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (64+i)) 15 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (64+i)) 15 (64+i)
    (validAll 15 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part9 : ∀ i ∈ List.range 8, CorrectAt 15 (72+i) := by
  decide +kernel

theorem base_r15_part9 : ∀ i ∈ List.range 8, BaseCheckAt 15 (72+i) := by
  decide +kernel

theorem strict_r15_part9 : ∀ i ∈ List.range 8, StrictCheckAt 15 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (72+i)) 15 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (72+i)) 15 (72+i)
    (validAll 15 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part10 : ∀ i ∈ List.range 8, CorrectAt 15 (80+i) := by
  decide +kernel

theorem base_r15_part10 : ∀ i ∈ List.range 8, BaseCheckAt 15 (80+i) := by
  decide +kernel

theorem strict_r15_part10 : ∀ i ∈ List.range 8, StrictCheckAt 15 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (80+i)) 15 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (80+i)) 15 (80+i)
    (validAll 15 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part11 : ∀ i ∈ List.range 8, CorrectAt 15 (88+i) := by
  decide +kernel

theorem base_r15_part11 : ∀ i ∈ List.range 8, BaseCheckAt 15 (88+i) := by
  decide +kernel

theorem strict_r15_part11 : ∀ i ∈ List.range 8, StrictCheckAt 15 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (88+i)) 15 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (88+i)) 15 (88+i)
    (validAll 15 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part12 : ∀ i ∈ List.range 8, CorrectAt 15 (96+i) := by
  decide +kernel

theorem base_r15_part12 : ∀ i ∈ List.range 8, BaseCheckAt 15 (96+i) := by
  decide +kernel

theorem strict_r15_part12 : ∀ i ∈ List.range 8, StrictCheckAt 15 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (96+i)) 15 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (96+i)) 15 (96+i)
    (validAll 15 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part13 : ∀ i ∈ List.range 8, CorrectAt 15 (104+i) := by
  decide +kernel

theorem base_r15_part13 : ∀ i ∈ List.range 8, BaseCheckAt 15 (104+i) := by
  decide +kernel

theorem strict_r15_part13 : ∀ i ∈ List.range 8, StrictCheckAt 15 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (104+i)) 15 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (104+i)) 15 (104+i)
    (validAll 15 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part14 : ∀ i ∈ List.range 8, CorrectAt 15 (112+i) := by
  decide +kernel

theorem base_r15_part14 : ∀ i ∈ List.range 8, BaseCheckAt 15 (112+i) := by
  decide +kernel

theorem strict_r15_part14 : ∀ i ∈ List.range 8, StrictCheckAt 15 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 15 (112+i)) 15 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (112+i)) 15 (112+i)
    (validAll 15 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r15_part15 : ∀ i ∈ List.range 5, CorrectAt 15 (120+i) := by
  decide +kernel

theorem base_r15_part15 : ∀ i ∈ List.range 5, BaseCheckAt 15 (120+i) := by
  decide +kernel

theorem strict_r15_part15 : ∀ i ∈ List.range 5, StrictCheckAt 15 (120+i) := by
  have hfast : ∀ i ∈ List.range 5, StrictAtFast (row 15 (120+i)) 15 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 5 := List.mem_range.mp hi
  exact strictAtFast_sound (row 15 (120+i)) 15 (120+i)
    (validAll 15 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
