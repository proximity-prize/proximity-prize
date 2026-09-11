import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r19_part0 : ∀ i ∈ List.range 8, CorrectAt 19 (0+i) := by
  decide +kernel

theorem base_r19_part0 : ∀ i ∈ List.range 8, BaseCheckAt 19 (0+i) := by
  decide +kernel

theorem strict_r19_part0 : ∀ i ∈ List.range 8, StrictCheckAt 19 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (0+i)) 19 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (0+i)) 19 (0+i)
    (validAll 19 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part1 : ∀ i ∈ List.range 8, CorrectAt 19 (8+i) := by
  decide +kernel

theorem base_r19_part1 : ∀ i ∈ List.range 8, BaseCheckAt 19 (8+i) := by
  decide +kernel

theorem strict_r19_part1 : ∀ i ∈ List.range 8, StrictCheckAt 19 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (8+i)) 19 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (8+i)) 19 (8+i)
    (validAll 19 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part2 : ∀ i ∈ List.range 8, CorrectAt 19 (16+i) := by
  decide +kernel

theorem base_r19_part2 : ∀ i ∈ List.range 8, BaseCheckAt 19 (16+i) := by
  decide +kernel

theorem strict_r19_part2 : ∀ i ∈ List.range 8, StrictCheckAt 19 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (16+i)) 19 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (16+i)) 19 (16+i)
    (validAll 19 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part3 : ∀ i ∈ List.range 8, CorrectAt 19 (24+i) := by
  decide +kernel

theorem base_r19_part3 : ∀ i ∈ List.range 8, BaseCheckAt 19 (24+i) := by
  decide +kernel

theorem strict_r19_part3 : ∀ i ∈ List.range 8, StrictCheckAt 19 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (24+i)) 19 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (24+i)) 19 (24+i)
    (validAll 19 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part4 : ∀ i ∈ List.range 8, CorrectAt 19 (32+i) := by
  decide +kernel

theorem base_r19_part4 : ∀ i ∈ List.range 8, BaseCheckAt 19 (32+i) := by
  decide +kernel

theorem strict_r19_part4 : ∀ i ∈ List.range 8, StrictCheckAt 19 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (32+i)) 19 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (32+i)) 19 (32+i)
    (validAll 19 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part5 : ∀ i ∈ List.range 8, CorrectAt 19 (40+i) := by
  decide +kernel

theorem base_r19_part5 : ∀ i ∈ List.range 8, BaseCheckAt 19 (40+i) := by
  decide +kernel

theorem strict_r19_part5 : ∀ i ∈ List.range 8, StrictCheckAt 19 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (40+i)) 19 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (40+i)) 19 (40+i)
    (validAll 19 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part6 : ∀ i ∈ List.range 8, CorrectAt 19 (48+i) := by
  decide +kernel

theorem base_r19_part6 : ∀ i ∈ List.range 8, BaseCheckAt 19 (48+i) := by
  decide +kernel

theorem strict_r19_part6 : ∀ i ∈ List.range 8, StrictCheckAt 19 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (48+i)) 19 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (48+i)) 19 (48+i)
    (validAll 19 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part7 : ∀ i ∈ List.range 8, CorrectAt 19 (56+i) := by
  decide +kernel

theorem base_r19_part7 : ∀ i ∈ List.range 8, BaseCheckAt 19 (56+i) := by
  decide +kernel

theorem strict_r19_part7 : ∀ i ∈ List.range 8, StrictCheckAt 19 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (56+i)) 19 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (56+i)) 19 (56+i)
    (validAll 19 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part8 : ∀ i ∈ List.range 8, CorrectAt 19 (64+i) := by
  decide +kernel

theorem base_r19_part8 : ∀ i ∈ List.range 8, BaseCheckAt 19 (64+i) := by
  decide +kernel

theorem strict_r19_part8 : ∀ i ∈ List.range 8, StrictCheckAt 19 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (64+i)) 19 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (64+i)) 19 (64+i)
    (validAll 19 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part9 : ∀ i ∈ List.range 8, CorrectAt 19 (72+i) := by
  decide +kernel

theorem base_r19_part9 : ∀ i ∈ List.range 8, BaseCheckAt 19 (72+i) := by
  decide +kernel

theorem strict_r19_part9 : ∀ i ∈ List.range 8, StrictCheckAt 19 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (72+i)) 19 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (72+i)) 19 (72+i)
    (validAll 19 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part10 : ∀ i ∈ List.range 8, CorrectAt 19 (80+i) := by
  decide +kernel

theorem base_r19_part10 : ∀ i ∈ List.range 8, BaseCheckAt 19 (80+i) := by
  decide +kernel

theorem strict_r19_part10 : ∀ i ∈ List.range 8, StrictCheckAt 19 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (80+i)) 19 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (80+i)) 19 (80+i)
    (validAll 19 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part11 : ∀ i ∈ List.range 8, CorrectAt 19 (88+i) := by
  decide +kernel

theorem base_r19_part11 : ∀ i ∈ List.range 8, BaseCheckAt 19 (88+i) := by
  decide +kernel

theorem strict_r19_part11 : ∀ i ∈ List.range 8, StrictCheckAt 19 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (88+i)) 19 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (88+i)) 19 (88+i)
    (validAll 19 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part12 : ∀ i ∈ List.range 8, CorrectAt 19 (96+i) := by
  decide +kernel

theorem base_r19_part12 : ∀ i ∈ List.range 8, BaseCheckAt 19 (96+i) := by
  decide +kernel

theorem strict_r19_part12 : ∀ i ∈ List.range 8, StrictCheckAt 19 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (96+i)) 19 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (96+i)) 19 (96+i)
    (validAll 19 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part13 : ∀ i ∈ List.range 8, CorrectAt 19 (104+i) := by
  decide +kernel

theorem base_r19_part13 : ∀ i ∈ List.range 8, BaseCheckAt 19 (104+i) := by
  decide +kernel

theorem strict_r19_part13 : ∀ i ∈ List.range 8, StrictCheckAt 19 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (104+i)) 19 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (104+i)) 19 (104+i)
    (validAll 19 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part14 : ∀ i ∈ List.range 8, CorrectAt 19 (112+i) := by
  decide +kernel

theorem base_r19_part14 : ∀ i ∈ List.range 8, BaseCheckAt 19 (112+i) := by
  decide +kernel

theorem strict_r19_part14 : ∀ i ∈ List.range 8, StrictCheckAt 19 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 19 (112+i)) 19 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (112+i)) 19 (112+i)
    (validAll 19 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r19_part15 : ∀ i ∈ List.range 1, CorrectAt 19 (120+i) := by
  decide +kernel

theorem base_r19_part15 : ∀ i ∈ List.range 1, BaseCheckAt 19 (120+i) := by
  decide +kernel

theorem strict_r19_part15 : ∀ i ∈ List.range 1, StrictCheckAt 19 (120+i) := by
  have hfast : ∀ i ∈ List.range 1, StrictAtFast (row 19 (120+i)) 19 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 1 := List.mem_range.mp hi
  exact strictAtFast_sound (row 19 (120+i)) 19 (120+i)
    (validAll 19 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
