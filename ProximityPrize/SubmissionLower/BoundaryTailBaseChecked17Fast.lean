import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r17_part0 : ∀ i ∈ List.range 8, CorrectAt 17 (0+i) := by
  decide +kernel

theorem base_r17_part0 : ∀ i ∈ List.range 8, BaseCheckAt 17 (0+i) := by
  decide +kernel

theorem strict_r17_part0 : ∀ i ∈ List.range 8, StrictCheckAt 17 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (0+i)) 17 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (0+i)) 17 (0+i)
    (validAll 17 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part1 : ∀ i ∈ List.range 8, CorrectAt 17 (8+i) := by
  decide +kernel

theorem base_r17_part1 : ∀ i ∈ List.range 8, BaseCheckAt 17 (8+i) := by
  decide +kernel

theorem strict_r17_part1 : ∀ i ∈ List.range 8, StrictCheckAt 17 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (8+i)) 17 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (8+i)) 17 (8+i)
    (validAll 17 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part2 : ∀ i ∈ List.range 8, CorrectAt 17 (16+i) := by
  decide +kernel

theorem base_r17_part2 : ∀ i ∈ List.range 8, BaseCheckAt 17 (16+i) := by
  decide +kernel

theorem strict_r17_part2 : ∀ i ∈ List.range 8, StrictCheckAt 17 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (16+i)) 17 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (16+i)) 17 (16+i)
    (validAll 17 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part3 : ∀ i ∈ List.range 8, CorrectAt 17 (24+i) := by
  decide +kernel

theorem base_r17_part3 : ∀ i ∈ List.range 8, BaseCheckAt 17 (24+i) := by
  decide +kernel

theorem strict_r17_part3 : ∀ i ∈ List.range 8, StrictCheckAt 17 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (24+i)) 17 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (24+i)) 17 (24+i)
    (validAll 17 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part4 : ∀ i ∈ List.range 8, CorrectAt 17 (32+i) := by
  decide +kernel

theorem base_r17_part4 : ∀ i ∈ List.range 8, BaseCheckAt 17 (32+i) := by
  decide +kernel

theorem strict_r17_part4 : ∀ i ∈ List.range 8, StrictCheckAt 17 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (32+i)) 17 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (32+i)) 17 (32+i)
    (validAll 17 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part5 : ∀ i ∈ List.range 8, CorrectAt 17 (40+i) := by
  decide +kernel

theorem base_r17_part5 : ∀ i ∈ List.range 8, BaseCheckAt 17 (40+i) := by
  decide +kernel

theorem strict_r17_part5 : ∀ i ∈ List.range 8, StrictCheckAt 17 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (40+i)) 17 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (40+i)) 17 (40+i)
    (validAll 17 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part6 : ∀ i ∈ List.range 8, CorrectAt 17 (48+i) := by
  decide +kernel

theorem base_r17_part6 : ∀ i ∈ List.range 8, BaseCheckAt 17 (48+i) := by
  decide +kernel

theorem strict_r17_part6 : ∀ i ∈ List.range 8, StrictCheckAt 17 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (48+i)) 17 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (48+i)) 17 (48+i)
    (validAll 17 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part7 : ∀ i ∈ List.range 8, CorrectAt 17 (56+i) := by
  decide +kernel

theorem base_r17_part7 : ∀ i ∈ List.range 8, BaseCheckAt 17 (56+i) := by
  decide +kernel

theorem strict_r17_part7 : ∀ i ∈ List.range 8, StrictCheckAt 17 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (56+i)) 17 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (56+i)) 17 (56+i)
    (validAll 17 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part8 : ∀ i ∈ List.range 8, CorrectAt 17 (64+i) := by
  decide +kernel

theorem base_r17_part8 : ∀ i ∈ List.range 8, BaseCheckAt 17 (64+i) := by
  decide +kernel

theorem strict_r17_part8 : ∀ i ∈ List.range 8, StrictCheckAt 17 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (64+i)) 17 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (64+i)) 17 (64+i)
    (validAll 17 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part9 : ∀ i ∈ List.range 8, CorrectAt 17 (72+i) := by
  decide +kernel

theorem base_r17_part9 : ∀ i ∈ List.range 8, BaseCheckAt 17 (72+i) := by
  decide +kernel

theorem strict_r17_part9 : ∀ i ∈ List.range 8, StrictCheckAt 17 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (72+i)) 17 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (72+i)) 17 (72+i)
    (validAll 17 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part10 : ∀ i ∈ List.range 8, CorrectAt 17 (80+i) := by
  decide +kernel

theorem base_r17_part10 : ∀ i ∈ List.range 8, BaseCheckAt 17 (80+i) := by
  decide +kernel

theorem strict_r17_part10 : ∀ i ∈ List.range 8, StrictCheckAt 17 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (80+i)) 17 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (80+i)) 17 (80+i)
    (validAll 17 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part11 : ∀ i ∈ List.range 8, CorrectAt 17 (88+i) := by
  decide +kernel

theorem base_r17_part11 : ∀ i ∈ List.range 8, BaseCheckAt 17 (88+i) := by
  decide +kernel

theorem strict_r17_part11 : ∀ i ∈ List.range 8, StrictCheckAt 17 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (88+i)) 17 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (88+i)) 17 (88+i)
    (validAll 17 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part12 : ∀ i ∈ List.range 8, CorrectAt 17 (96+i) := by
  decide +kernel

theorem base_r17_part12 : ∀ i ∈ List.range 8, BaseCheckAt 17 (96+i) := by
  decide +kernel

theorem strict_r17_part12 : ∀ i ∈ List.range 8, StrictCheckAt 17 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (96+i)) 17 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (96+i)) 17 (96+i)
    (validAll 17 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part13 : ∀ i ∈ List.range 8, CorrectAt 17 (104+i) := by
  decide +kernel

theorem base_r17_part13 : ∀ i ∈ List.range 8, BaseCheckAt 17 (104+i) := by
  decide +kernel

theorem strict_r17_part13 : ∀ i ∈ List.range 8, StrictCheckAt 17 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (104+i)) 17 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (104+i)) 17 (104+i)
    (validAll 17 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part14 : ∀ i ∈ List.range 8, CorrectAt 17 (112+i) := by
  decide +kernel

theorem base_r17_part14 : ∀ i ∈ List.range 8, BaseCheckAt 17 (112+i) := by
  decide +kernel

theorem strict_r17_part14 : ∀ i ∈ List.range 8, StrictCheckAt 17 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 17 (112+i)) 17 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (112+i)) 17 (112+i)
    (validAll 17 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r17_part15 : ∀ i ∈ List.range 3, CorrectAt 17 (120+i) := by
  decide +kernel

theorem base_r17_part15 : ∀ i ∈ List.range 3, BaseCheckAt 17 (120+i) := by
  decide +kernel

theorem strict_r17_part15 : ∀ i ∈ List.range 3, StrictCheckAt 17 (120+i) := by
  have hfast : ∀ i ∈ List.range 3, StrictAtFast (row 17 (120+i)) 17 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 3 := List.mem_range.mp hi
  exact strictAtFast_sound (row 17 (120+i)) 17 (120+i)
    (validAll 17 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
