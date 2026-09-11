import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r10_part0 : ∀ i ∈ List.range 8, CorrectAt 10 (0+i) := by
  decide +kernel

theorem base_r10_part0 : ∀ i ∈ List.range 8, BaseCheckAt 10 (0+i) := by
  decide +kernel

theorem strict_r10_part0 : ∀ i ∈ List.range 8, StrictCheckAt 10 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (0+i)) 10 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (0+i)) 10 (0+i)
    (validAll 10 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part1 : ∀ i ∈ List.range 8, CorrectAt 10 (8+i) := by
  decide +kernel

theorem base_r10_part1 : ∀ i ∈ List.range 8, BaseCheckAt 10 (8+i) := by
  decide +kernel

theorem strict_r10_part1 : ∀ i ∈ List.range 8, StrictCheckAt 10 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (8+i)) 10 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (8+i)) 10 (8+i)
    (validAll 10 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part2 : ∀ i ∈ List.range 8, CorrectAt 10 (16+i) := by
  decide +kernel

theorem base_r10_part2 : ∀ i ∈ List.range 8, BaseCheckAt 10 (16+i) := by
  decide +kernel

theorem strict_r10_part2 : ∀ i ∈ List.range 8, StrictCheckAt 10 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (16+i)) 10 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (16+i)) 10 (16+i)
    (validAll 10 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part3 : ∀ i ∈ List.range 8, CorrectAt 10 (24+i) := by
  decide +kernel

theorem base_r10_part3 : ∀ i ∈ List.range 8, BaseCheckAt 10 (24+i) := by
  decide +kernel

theorem strict_r10_part3 : ∀ i ∈ List.range 8, StrictCheckAt 10 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (24+i)) 10 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (24+i)) 10 (24+i)
    (validAll 10 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part4 : ∀ i ∈ List.range 8, CorrectAt 10 (32+i) := by
  decide +kernel

theorem base_r10_part4 : ∀ i ∈ List.range 8, BaseCheckAt 10 (32+i) := by
  decide +kernel

theorem strict_r10_part4 : ∀ i ∈ List.range 8, StrictCheckAt 10 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (32+i)) 10 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (32+i)) 10 (32+i)
    (validAll 10 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part5 : ∀ i ∈ List.range 8, CorrectAt 10 (40+i) := by
  decide +kernel

theorem base_r10_part5 : ∀ i ∈ List.range 8, BaseCheckAt 10 (40+i) := by
  decide +kernel

theorem strict_r10_part5 : ∀ i ∈ List.range 8, StrictCheckAt 10 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (40+i)) 10 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (40+i)) 10 (40+i)
    (validAll 10 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part6 : ∀ i ∈ List.range 8, CorrectAt 10 (48+i) := by
  decide +kernel

theorem base_r10_part6 : ∀ i ∈ List.range 8, BaseCheckAt 10 (48+i) := by
  decide +kernel

theorem strict_r10_part6 : ∀ i ∈ List.range 8, StrictCheckAt 10 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (48+i)) 10 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (48+i)) 10 (48+i)
    (validAll 10 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part7 : ∀ i ∈ List.range 8, CorrectAt 10 (56+i) := by
  decide +kernel

theorem base_r10_part7 : ∀ i ∈ List.range 8, BaseCheckAt 10 (56+i) := by
  decide +kernel

theorem strict_r10_part7 : ∀ i ∈ List.range 8, StrictCheckAt 10 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (56+i)) 10 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (56+i)) 10 (56+i)
    (validAll 10 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part8 : ∀ i ∈ List.range 8, CorrectAt 10 (64+i) := by
  decide +kernel

theorem base_r10_part8 : ∀ i ∈ List.range 8, BaseCheckAt 10 (64+i) := by
  decide +kernel

theorem strict_r10_part8 : ∀ i ∈ List.range 8, StrictCheckAt 10 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (64+i)) 10 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (64+i)) 10 (64+i)
    (validAll 10 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part9 : ∀ i ∈ List.range 8, CorrectAt 10 (72+i) := by
  decide +kernel

theorem base_r10_part9 : ∀ i ∈ List.range 8, BaseCheckAt 10 (72+i) := by
  decide +kernel

theorem strict_r10_part9 : ∀ i ∈ List.range 8, StrictCheckAt 10 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (72+i)) 10 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (72+i)) 10 (72+i)
    (validAll 10 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part10 : ∀ i ∈ List.range 8, CorrectAt 10 (80+i) := by
  decide +kernel

theorem base_r10_part10 : ∀ i ∈ List.range 8, BaseCheckAt 10 (80+i) := by
  decide +kernel

theorem strict_r10_part10 : ∀ i ∈ List.range 8, StrictCheckAt 10 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (80+i)) 10 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (80+i)) 10 (80+i)
    (validAll 10 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part11 : ∀ i ∈ List.range 8, CorrectAt 10 (88+i) := by
  decide +kernel

theorem base_r10_part11 : ∀ i ∈ List.range 8, BaseCheckAt 10 (88+i) := by
  decide +kernel

theorem strict_r10_part11 : ∀ i ∈ List.range 8, StrictCheckAt 10 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (88+i)) 10 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (88+i)) 10 (88+i)
    (validAll 10 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part12 : ∀ i ∈ List.range 8, CorrectAt 10 (96+i) := by
  decide +kernel

theorem base_r10_part12 : ∀ i ∈ List.range 8, BaseCheckAt 10 (96+i) := by
  decide +kernel

theorem strict_r10_part12 : ∀ i ∈ List.range 8, StrictCheckAt 10 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (96+i)) 10 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (96+i)) 10 (96+i)
    (validAll 10 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part13 : ∀ i ∈ List.range 8, CorrectAt 10 (104+i) := by
  decide +kernel

theorem base_r10_part13 : ∀ i ∈ List.range 8, BaseCheckAt 10 (104+i) := by
  decide +kernel

theorem strict_r10_part13 : ∀ i ∈ List.range 8, StrictCheckAt 10 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (104+i)) 10 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (104+i)) 10 (104+i)
    (validAll 10 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part14 : ∀ i ∈ List.range 8, CorrectAt 10 (112+i) := by
  decide +kernel

theorem base_r10_part14 : ∀ i ∈ List.range 8, BaseCheckAt 10 (112+i) := by
  decide +kernel

theorem strict_r10_part14 : ∀ i ∈ List.range 8, StrictCheckAt 10 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (112+i)) 10 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (112+i)) 10 (112+i)
    (validAll 10 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part15 : ∀ i ∈ List.range 8, CorrectAt 10 (120+i) := by
  decide +kernel

theorem base_r10_part15 : ∀ i ∈ List.range 8, BaseCheckAt 10 (120+i) := by
  decide +kernel

theorem strict_r10_part15 : ∀ i ∈ List.range 8, StrictCheckAt 10 (120+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 10 (120+i)) 10 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (120+i)) 10 (120+i)
    (validAll 10 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r10_part16 : ∀ i ∈ List.range 2, CorrectAt 10 (128+i) := by
  decide +kernel

theorem base_r10_part16 : ∀ i ∈ List.range 2, BaseCheckAt 10 (128+i) := by
  decide +kernel

theorem strict_r10_part16 : ∀ i ∈ List.range 2, StrictCheckAt 10 (128+i) := by
  have hfast : ∀ i ∈ List.range 2, StrictAtFast (row 10 (128+i)) 10 (128+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 2 := List.mem_range.mp hi
  exact strictAtFast_sound (row 10 (128+i)) 10 (128+i)
    (validAll 10 (128+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
