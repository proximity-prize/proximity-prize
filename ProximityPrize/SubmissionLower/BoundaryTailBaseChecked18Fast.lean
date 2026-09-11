import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r18_part0 : ∀ i ∈ List.range 8, CorrectAt 18 (0+i) := by
  decide +kernel

theorem base_r18_part0 : ∀ i ∈ List.range 8, BaseCheckAt 18 (0+i) := by
  decide +kernel

theorem strict_r18_part0 : ∀ i ∈ List.range 8, StrictCheckAt 18 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (0+i)) 18 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (0+i)) 18 (0+i)
    (validAll 18 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part1 : ∀ i ∈ List.range 8, CorrectAt 18 (8+i) := by
  decide +kernel

theorem base_r18_part1 : ∀ i ∈ List.range 8, BaseCheckAt 18 (8+i) := by
  decide +kernel

theorem strict_r18_part1 : ∀ i ∈ List.range 8, StrictCheckAt 18 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (8+i)) 18 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (8+i)) 18 (8+i)
    (validAll 18 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part2 : ∀ i ∈ List.range 8, CorrectAt 18 (16+i) := by
  decide +kernel

theorem base_r18_part2 : ∀ i ∈ List.range 8, BaseCheckAt 18 (16+i) := by
  decide +kernel

theorem strict_r18_part2 : ∀ i ∈ List.range 8, StrictCheckAt 18 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (16+i)) 18 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (16+i)) 18 (16+i)
    (validAll 18 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part3 : ∀ i ∈ List.range 8, CorrectAt 18 (24+i) := by
  decide +kernel

theorem base_r18_part3 : ∀ i ∈ List.range 8, BaseCheckAt 18 (24+i) := by
  decide +kernel

theorem strict_r18_part3 : ∀ i ∈ List.range 8, StrictCheckAt 18 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (24+i)) 18 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (24+i)) 18 (24+i)
    (validAll 18 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part4 : ∀ i ∈ List.range 8, CorrectAt 18 (32+i) := by
  decide +kernel

theorem base_r18_part4 : ∀ i ∈ List.range 8, BaseCheckAt 18 (32+i) := by
  decide +kernel

theorem strict_r18_part4 : ∀ i ∈ List.range 8, StrictCheckAt 18 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (32+i)) 18 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (32+i)) 18 (32+i)
    (validAll 18 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part5 : ∀ i ∈ List.range 8, CorrectAt 18 (40+i) := by
  decide +kernel

theorem base_r18_part5 : ∀ i ∈ List.range 8, BaseCheckAt 18 (40+i) := by
  decide +kernel

theorem strict_r18_part5 : ∀ i ∈ List.range 8, StrictCheckAt 18 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (40+i)) 18 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (40+i)) 18 (40+i)
    (validAll 18 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part6 : ∀ i ∈ List.range 8, CorrectAt 18 (48+i) := by
  decide +kernel

theorem base_r18_part6 : ∀ i ∈ List.range 8, BaseCheckAt 18 (48+i) := by
  decide +kernel

theorem strict_r18_part6 : ∀ i ∈ List.range 8, StrictCheckAt 18 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (48+i)) 18 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (48+i)) 18 (48+i)
    (validAll 18 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part7 : ∀ i ∈ List.range 8, CorrectAt 18 (56+i) := by
  decide +kernel

theorem base_r18_part7 : ∀ i ∈ List.range 8, BaseCheckAt 18 (56+i) := by
  decide +kernel

theorem strict_r18_part7 : ∀ i ∈ List.range 8, StrictCheckAt 18 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (56+i)) 18 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (56+i)) 18 (56+i)
    (validAll 18 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part8 : ∀ i ∈ List.range 8, CorrectAt 18 (64+i) := by
  decide +kernel

theorem base_r18_part8 : ∀ i ∈ List.range 8, BaseCheckAt 18 (64+i) := by
  decide +kernel

theorem strict_r18_part8 : ∀ i ∈ List.range 8, StrictCheckAt 18 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (64+i)) 18 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (64+i)) 18 (64+i)
    (validAll 18 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part9 : ∀ i ∈ List.range 8, CorrectAt 18 (72+i) := by
  decide +kernel

theorem base_r18_part9 : ∀ i ∈ List.range 8, BaseCheckAt 18 (72+i) := by
  decide +kernel

theorem strict_r18_part9 : ∀ i ∈ List.range 8, StrictCheckAt 18 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (72+i)) 18 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (72+i)) 18 (72+i)
    (validAll 18 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part10 : ∀ i ∈ List.range 8, CorrectAt 18 (80+i) := by
  decide +kernel

theorem base_r18_part10 : ∀ i ∈ List.range 8, BaseCheckAt 18 (80+i) := by
  decide +kernel

theorem strict_r18_part10 : ∀ i ∈ List.range 8, StrictCheckAt 18 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (80+i)) 18 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (80+i)) 18 (80+i)
    (validAll 18 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part11 : ∀ i ∈ List.range 8, CorrectAt 18 (88+i) := by
  decide +kernel

theorem base_r18_part11 : ∀ i ∈ List.range 8, BaseCheckAt 18 (88+i) := by
  decide +kernel

theorem strict_r18_part11 : ∀ i ∈ List.range 8, StrictCheckAt 18 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (88+i)) 18 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (88+i)) 18 (88+i)
    (validAll 18 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part12 : ∀ i ∈ List.range 8, CorrectAt 18 (96+i) := by
  decide +kernel

theorem base_r18_part12 : ∀ i ∈ List.range 8, BaseCheckAt 18 (96+i) := by
  decide +kernel

theorem strict_r18_part12 : ∀ i ∈ List.range 8, StrictCheckAt 18 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (96+i)) 18 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (96+i)) 18 (96+i)
    (validAll 18 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part13 : ∀ i ∈ List.range 8, CorrectAt 18 (104+i) := by
  decide +kernel

theorem base_r18_part13 : ∀ i ∈ List.range 8, BaseCheckAt 18 (104+i) := by
  decide +kernel

theorem strict_r18_part13 : ∀ i ∈ List.range 8, StrictCheckAt 18 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (104+i)) 18 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (104+i)) 18 (104+i)
    (validAll 18 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part14 : ∀ i ∈ List.range 8, CorrectAt 18 (112+i) := by
  decide +kernel

theorem base_r18_part14 : ∀ i ∈ List.range 8, BaseCheckAt 18 (112+i) := by
  decide +kernel

theorem strict_r18_part14 : ∀ i ∈ List.range 8, StrictCheckAt 18 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 18 (112+i)) 18 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (112+i)) 18 (112+i)
    (validAll 18 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r18_part15 : ∀ i ∈ List.range 2, CorrectAt 18 (120+i) := by
  decide +kernel

theorem base_r18_part15 : ∀ i ∈ List.range 2, BaseCheckAt 18 (120+i) := by
  decide +kernel

theorem strict_r18_part15 : ∀ i ∈ List.range 2, StrictCheckAt 18 (120+i) := by
  have hfast : ∀ i ∈ List.range 2, StrictAtFast (row 18 (120+i)) 18 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 2 := List.mem_range.mp hi
  exact strictAtFast_sound (row 18 (120+i)) 18 (120+i)
    (validAll 18 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
