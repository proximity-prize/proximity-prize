import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r14_part0 : ∀ i ∈ List.range 8, CorrectAt 14 (0+i) := by
  decide +kernel

theorem base_r14_part0 : ∀ i ∈ List.range 8, BaseCheckAt 14 (0+i) := by
  decide +kernel

theorem strict_r14_part0 : ∀ i ∈ List.range 8, StrictCheckAt 14 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (0+i)) 14 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (0+i)) 14 (0+i)
    (validAll 14 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part1 : ∀ i ∈ List.range 8, CorrectAt 14 (8+i) := by
  decide +kernel

theorem base_r14_part1 : ∀ i ∈ List.range 8, BaseCheckAt 14 (8+i) := by
  decide +kernel

theorem strict_r14_part1 : ∀ i ∈ List.range 8, StrictCheckAt 14 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (8+i)) 14 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (8+i)) 14 (8+i)
    (validAll 14 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part2 : ∀ i ∈ List.range 8, CorrectAt 14 (16+i) := by
  decide +kernel

theorem base_r14_part2 : ∀ i ∈ List.range 8, BaseCheckAt 14 (16+i) := by
  decide +kernel

theorem strict_r14_part2 : ∀ i ∈ List.range 8, StrictCheckAt 14 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (16+i)) 14 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (16+i)) 14 (16+i)
    (validAll 14 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part3 : ∀ i ∈ List.range 8, CorrectAt 14 (24+i) := by
  decide +kernel

theorem base_r14_part3 : ∀ i ∈ List.range 8, BaseCheckAt 14 (24+i) := by
  decide +kernel

theorem strict_r14_part3 : ∀ i ∈ List.range 8, StrictCheckAt 14 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (24+i)) 14 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (24+i)) 14 (24+i)
    (validAll 14 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part4 : ∀ i ∈ List.range 8, CorrectAt 14 (32+i) := by
  decide +kernel

theorem base_r14_part4 : ∀ i ∈ List.range 8, BaseCheckAt 14 (32+i) := by
  decide +kernel

theorem strict_r14_part4 : ∀ i ∈ List.range 8, StrictCheckAt 14 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (32+i)) 14 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (32+i)) 14 (32+i)
    (validAll 14 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part5 : ∀ i ∈ List.range 8, CorrectAt 14 (40+i) := by
  decide +kernel

theorem base_r14_part5 : ∀ i ∈ List.range 8, BaseCheckAt 14 (40+i) := by
  decide +kernel

theorem strict_r14_part5 : ∀ i ∈ List.range 8, StrictCheckAt 14 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (40+i)) 14 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (40+i)) 14 (40+i)
    (validAll 14 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part6 : ∀ i ∈ List.range 8, CorrectAt 14 (48+i) := by
  decide +kernel

theorem base_r14_part6 : ∀ i ∈ List.range 8, BaseCheckAt 14 (48+i) := by
  decide +kernel

theorem strict_r14_part6 : ∀ i ∈ List.range 8, StrictCheckAt 14 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (48+i)) 14 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (48+i)) 14 (48+i)
    (validAll 14 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part7 : ∀ i ∈ List.range 8, CorrectAt 14 (56+i) := by
  decide +kernel

theorem base_r14_part7 : ∀ i ∈ List.range 8, BaseCheckAt 14 (56+i) := by
  decide +kernel

theorem strict_r14_part7 : ∀ i ∈ List.range 8, StrictCheckAt 14 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (56+i)) 14 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (56+i)) 14 (56+i)
    (validAll 14 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part8 : ∀ i ∈ List.range 8, CorrectAt 14 (64+i) := by
  decide +kernel

theorem base_r14_part8 : ∀ i ∈ List.range 8, BaseCheckAt 14 (64+i) := by
  decide +kernel

theorem strict_r14_part8 : ∀ i ∈ List.range 8, StrictCheckAt 14 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (64+i)) 14 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (64+i)) 14 (64+i)
    (validAll 14 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part9 : ∀ i ∈ List.range 8, CorrectAt 14 (72+i) := by
  decide +kernel

theorem base_r14_part9 : ∀ i ∈ List.range 8, BaseCheckAt 14 (72+i) := by
  decide +kernel

theorem strict_r14_part9 : ∀ i ∈ List.range 8, StrictCheckAt 14 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (72+i)) 14 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (72+i)) 14 (72+i)
    (validAll 14 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part10 : ∀ i ∈ List.range 8, CorrectAt 14 (80+i) := by
  decide +kernel

theorem base_r14_part10 : ∀ i ∈ List.range 8, BaseCheckAt 14 (80+i) := by
  decide +kernel

theorem strict_r14_part10 : ∀ i ∈ List.range 8, StrictCheckAt 14 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (80+i)) 14 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (80+i)) 14 (80+i)
    (validAll 14 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part11 : ∀ i ∈ List.range 8, CorrectAt 14 (88+i) := by
  decide +kernel

theorem base_r14_part11 : ∀ i ∈ List.range 8, BaseCheckAt 14 (88+i) := by
  decide +kernel

theorem strict_r14_part11 : ∀ i ∈ List.range 8, StrictCheckAt 14 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (88+i)) 14 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (88+i)) 14 (88+i)
    (validAll 14 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part12 : ∀ i ∈ List.range 8, CorrectAt 14 (96+i) := by
  decide +kernel

theorem base_r14_part12 : ∀ i ∈ List.range 8, BaseCheckAt 14 (96+i) := by
  decide +kernel

theorem strict_r14_part12 : ∀ i ∈ List.range 8, StrictCheckAt 14 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (96+i)) 14 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (96+i)) 14 (96+i)
    (validAll 14 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part13 : ∀ i ∈ List.range 8, CorrectAt 14 (104+i) := by
  decide +kernel

theorem base_r14_part13 : ∀ i ∈ List.range 8, BaseCheckAt 14 (104+i) := by
  decide +kernel

theorem strict_r14_part13 : ∀ i ∈ List.range 8, StrictCheckAt 14 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (104+i)) 14 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (104+i)) 14 (104+i)
    (validAll 14 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part14 : ∀ i ∈ List.range 8, CorrectAt 14 (112+i) := by
  decide +kernel

theorem base_r14_part14 : ∀ i ∈ List.range 8, BaseCheckAt 14 (112+i) := by
  decide +kernel

theorem strict_r14_part14 : ∀ i ∈ List.range 8, StrictCheckAt 14 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 14 (112+i)) 14 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (112+i)) 14 (112+i)
    (validAll 14 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r14_part15 : ∀ i ∈ List.range 6, CorrectAt 14 (120+i) := by
  decide +kernel

theorem base_r14_part15 : ∀ i ∈ List.range 6, BaseCheckAt 14 (120+i) := by
  decide +kernel

theorem strict_r14_part15 : ∀ i ∈ List.range 6, StrictCheckAt 14 (120+i) := by
  have hfast : ∀ i ∈ List.range 6, StrictAtFast (row 14 (120+i)) 14 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 6 := List.mem_range.mp hi
  exact strictAtFast_sound (row 14 (120+i)) 14 (120+i)
    (validAll 14 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
