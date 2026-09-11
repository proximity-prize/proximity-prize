import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r13_part0 : ∀ i ∈ List.range 8, CorrectAt 13 (0+i) := by
  decide +kernel

theorem base_r13_part0 : ∀ i ∈ List.range 8, BaseCheckAt 13 (0+i) := by
  decide +kernel

theorem strict_r13_part0 : ∀ i ∈ List.range 8, StrictCheckAt 13 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (0+i)) 13 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (0+i)) 13 (0+i)
    (validAll 13 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part1 : ∀ i ∈ List.range 8, CorrectAt 13 (8+i) := by
  decide +kernel

theorem base_r13_part1 : ∀ i ∈ List.range 8, BaseCheckAt 13 (8+i) := by
  decide +kernel

theorem strict_r13_part1 : ∀ i ∈ List.range 8, StrictCheckAt 13 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (8+i)) 13 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (8+i)) 13 (8+i)
    (validAll 13 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part2 : ∀ i ∈ List.range 8, CorrectAt 13 (16+i) := by
  decide +kernel

theorem base_r13_part2 : ∀ i ∈ List.range 8, BaseCheckAt 13 (16+i) := by
  decide +kernel

theorem strict_r13_part2 : ∀ i ∈ List.range 8, StrictCheckAt 13 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (16+i)) 13 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (16+i)) 13 (16+i)
    (validAll 13 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part3 : ∀ i ∈ List.range 8, CorrectAt 13 (24+i) := by
  decide +kernel

theorem base_r13_part3 : ∀ i ∈ List.range 8, BaseCheckAt 13 (24+i) := by
  decide +kernel

theorem strict_r13_part3 : ∀ i ∈ List.range 8, StrictCheckAt 13 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (24+i)) 13 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (24+i)) 13 (24+i)
    (validAll 13 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part4 : ∀ i ∈ List.range 8, CorrectAt 13 (32+i) := by
  decide +kernel

theorem base_r13_part4 : ∀ i ∈ List.range 8, BaseCheckAt 13 (32+i) := by
  decide +kernel

theorem strict_r13_part4 : ∀ i ∈ List.range 8, StrictCheckAt 13 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (32+i)) 13 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (32+i)) 13 (32+i)
    (validAll 13 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part5 : ∀ i ∈ List.range 8, CorrectAt 13 (40+i) := by
  decide +kernel

theorem base_r13_part5 : ∀ i ∈ List.range 8, BaseCheckAt 13 (40+i) := by
  decide +kernel

theorem strict_r13_part5 : ∀ i ∈ List.range 8, StrictCheckAt 13 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (40+i)) 13 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (40+i)) 13 (40+i)
    (validAll 13 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part6 : ∀ i ∈ List.range 8, CorrectAt 13 (48+i) := by
  decide +kernel

theorem base_r13_part6 : ∀ i ∈ List.range 8, BaseCheckAt 13 (48+i) := by
  decide +kernel

theorem strict_r13_part6 : ∀ i ∈ List.range 8, StrictCheckAt 13 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (48+i)) 13 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (48+i)) 13 (48+i)
    (validAll 13 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part7 : ∀ i ∈ List.range 8, CorrectAt 13 (56+i) := by
  decide +kernel

theorem base_r13_part7 : ∀ i ∈ List.range 8, BaseCheckAt 13 (56+i) := by
  decide +kernel

theorem strict_r13_part7 : ∀ i ∈ List.range 8, StrictCheckAt 13 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (56+i)) 13 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (56+i)) 13 (56+i)
    (validAll 13 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part8 : ∀ i ∈ List.range 8, CorrectAt 13 (64+i) := by
  decide +kernel

theorem base_r13_part8 : ∀ i ∈ List.range 8, BaseCheckAt 13 (64+i) := by
  decide +kernel

theorem strict_r13_part8 : ∀ i ∈ List.range 8, StrictCheckAt 13 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (64+i)) 13 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (64+i)) 13 (64+i)
    (validAll 13 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part9 : ∀ i ∈ List.range 8, CorrectAt 13 (72+i) := by
  decide +kernel

theorem base_r13_part9 : ∀ i ∈ List.range 8, BaseCheckAt 13 (72+i) := by
  decide +kernel

theorem strict_r13_part9 : ∀ i ∈ List.range 8, StrictCheckAt 13 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (72+i)) 13 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (72+i)) 13 (72+i)
    (validAll 13 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part10 : ∀ i ∈ List.range 8, CorrectAt 13 (80+i) := by
  decide +kernel

theorem base_r13_part10 : ∀ i ∈ List.range 8, BaseCheckAt 13 (80+i) := by
  decide +kernel

theorem strict_r13_part10 : ∀ i ∈ List.range 8, StrictCheckAt 13 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (80+i)) 13 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (80+i)) 13 (80+i)
    (validAll 13 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part11 : ∀ i ∈ List.range 8, CorrectAt 13 (88+i) := by
  decide +kernel

theorem base_r13_part11 : ∀ i ∈ List.range 8, BaseCheckAt 13 (88+i) := by
  decide +kernel

theorem strict_r13_part11 : ∀ i ∈ List.range 8, StrictCheckAt 13 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (88+i)) 13 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (88+i)) 13 (88+i)
    (validAll 13 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part12 : ∀ i ∈ List.range 8, CorrectAt 13 (96+i) := by
  decide +kernel

theorem base_r13_part12 : ∀ i ∈ List.range 8, BaseCheckAt 13 (96+i) := by
  decide +kernel

theorem strict_r13_part12 : ∀ i ∈ List.range 8, StrictCheckAt 13 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (96+i)) 13 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (96+i)) 13 (96+i)
    (validAll 13 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part13 : ∀ i ∈ List.range 8, CorrectAt 13 (104+i) := by
  decide +kernel

theorem base_r13_part13 : ∀ i ∈ List.range 8, BaseCheckAt 13 (104+i) := by
  decide +kernel

theorem strict_r13_part13 : ∀ i ∈ List.range 8, StrictCheckAt 13 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (104+i)) 13 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (104+i)) 13 (104+i)
    (validAll 13 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part14 : ∀ i ∈ List.range 8, CorrectAt 13 (112+i) := by
  decide +kernel

theorem base_r13_part14 : ∀ i ∈ List.range 8, BaseCheckAt 13 (112+i) := by
  decide +kernel

theorem strict_r13_part14 : ∀ i ∈ List.range 8, StrictCheckAt 13 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 13 (112+i)) 13 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (112+i)) 13 (112+i)
    (validAll 13 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r13_part15 : ∀ i ∈ List.range 7, CorrectAt 13 (120+i) := by
  decide +kernel

theorem base_r13_part15 : ∀ i ∈ List.range 7, BaseCheckAt 13 (120+i) := by
  decide +kernel

theorem strict_r13_part15 : ∀ i ∈ List.range 7, StrictCheckAt 13 (120+i) := by
  have hfast : ∀ i ∈ List.range 7, StrictAtFast (row 13 (120+i)) 13 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 7 := List.mem_range.mp hi
  exact strictAtFast_sound (row 13 (120+i)) 13 (120+i)
    (validAll 13 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
