import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r27_part0 : ∀ i ∈ List.range 8, CorrectAt 27 (0+i) := by
  decide +kernel

theorem base_r27_part0 : ∀ i ∈ List.range 8, BaseCheckAt 27 (0+i) := by
  decide +kernel

theorem strict_r27_part0 : ∀ i ∈ List.range 8, StrictCheckAt 27 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (0+i)) 27 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (0+i)) 27 (0+i)
    (validAll 27 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part1 : ∀ i ∈ List.range 8, CorrectAt 27 (8+i) := by
  decide +kernel

theorem base_r27_part1 : ∀ i ∈ List.range 8, BaseCheckAt 27 (8+i) := by
  decide +kernel

theorem strict_r27_part1 : ∀ i ∈ List.range 8, StrictCheckAt 27 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (8+i)) 27 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (8+i)) 27 (8+i)
    (validAll 27 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part2 : ∀ i ∈ List.range 8, CorrectAt 27 (16+i) := by
  decide +kernel

theorem base_r27_part2 : ∀ i ∈ List.range 8, BaseCheckAt 27 (16+i) := by
  decide +kernel

theorem strict_r27_part2 : ∀ i ∈ List.range 8, StrictCheckAt 27 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (16+i)) 27 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (16+i)) 27 (16+i)
    (validAll 27 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part3 : ∀ i ∈ List.range 8, CorrectAt 27 (24+i) := by
  decide +kernel

theorem base_r27_part3 : ∀ i ∈ List.range 8, BaseCheckAt 27 (24+i) := by
  decide +kernel

theorem strict_r27_part3 : ∀ i ∈ List.range 8, StrictCheckAt 27 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (24+i)) 27 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (24+i)) 27 (24+i)
    (validAll 27 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part4 : ∀ i ∈ List.range 8, CorrectAt 27 (32+i) := by
  decide +kernel

theorem base_r27_part4 : ∀ i ∈ List.range 8, BaseCheckAt 27 (32+i) := by
  decide +kernel

theorem strict_r27_part4 : ∀ i ∈ List.range 8, StrictCheckAt 27 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (32+i)) 27 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (32+i)) 27 (32+i)
    (validAll 27 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part5 : ∀ i ∈ List.range 8, CorrectAt 27 (40+i) := by
  decide +kernel

theorem base_r27_part5 : ∀ i ∈ List.range 8, BaseCheckAt 27 (40+i) := by
  decide +kernel

theorem strict_r27_part5 : ∀ i ∈ List.range 8, StrictCheckAt 27 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (40+i)) 27 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (40+i)) 27 (40+i)
    (validAll 27 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part6 : ∀ i ∈ List.range 8, CorrectAt 27 (48+i) := by
  decide +kernel

theorem base_r27_part6 : ∀ i ∈ List.range 8, BaseCheckAt 27 (48+i) := by
  decide +kernel

theorem strict_r27_part6 : ∀ i ∈ List.range 8, StrictCheckAt 27 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (48+i)) 27 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (48+i)) 27 (48+i)
    (validAll 27 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part7 : ∀ i ∈ List.range 8, CorrectAt 27 (56+i) := by
  decide +kernel

theorem base_r27_part7 : ∀ i ∈ List.range 8, BaseCheckAt 27 (56+i) := by
  decide +kernel

theorem strict_r27_part7 : ∀ i ∈ List.range 8, StrictCheckAt 27 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (56+i)) 27 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (56+i)) 27 (56+i)
    (validAll 27 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part8 : ∀ i ∈ List.range 8, CorrectAt 27 (64+i) := by
  decide +kernel

theorem base_r27_part8 : ∀ i ∈ List.range 8, BaseCheckAt 27 (64+i) := by
  decide +kernel

theorem strict_r27_part8 : ∀ i ∈ List.range 8, StrictCheckAt 27 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (64+i)) 27 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (64+i)) 27 (64+i)
    (validAll 27 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part9 : ∀ i ∈ List.range 8, CorrectAt 27 (72+i) := by
  decide +kernel

theorem base_r27_part9 : ∀ i ∈ List.range 8, BaseCheckAt 27 (72+i) := by
  decide +kernel

theorem strict_r27_part9 : ∀ i ∈ List.range 8, StrictCheckAt 27 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (72+i)) 27 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (72+i)) 27 (72+i)
    (validAll 27 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part10 : ∀ i ∈ List.range 8, CorrectAt 27 (80+i) := by
  decide +kernel

theorem base_r27_part10 : ∀ i ∈ List.range 8, BaseCheckAt 27 (80+i) := by
  decide +kernel

theorem strict_r27_part10 : ∀ i ∈ List.range 8, StrictCheckAt 27 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (80+i)) 27 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (80+i)) 27 (80+i)
    (validAll 27 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part11 : ∀ i ∈ List.range 8, CorrectAt 27 (88+i) := by
  decide +kernel

theorem base_r27_part11 : ∀ i ∈ List.range 8, BaseCheckAt 27 (88+i) := by
  decide +kernel

theorem strict_r27_part11 : ∀ i ∈ List.range 8, StrictCheckAt 27 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (88+i)) 27 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (88+i)) 27 (88+i)
    (validAll 27 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part12 : ∀ i ∈ List.range 8, CorrectAt 27 (96+i) := by
  decide +kernel

theorem base_r27_part12 : ∀ i ∈ List.range 8, BaseCheckAt 27 (96+i) := by
  decide +kernel

theorem strict_r27_part12 : ∀ i ∈ List.range 8, StrictCheckAt 27 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (96+i)) 27 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (96+i)) 27 (96+i)
    (validAll 27 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part13 : ∀ i ∈ List.range 8, CorrectAt 27 (104+i) := by
  decide +kernel

theorem base_r27_part13 : ∀ i ∈ List.range 8, BaseCheckAt 27 (104+i) := by
  decide +kernel

theorem strict_r27_part13 : ∀ i ∈ List.range 8, StrictCheckAt 27 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 27 (104+i)) 27 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (104+i)) 27 (104+i)
    (validAll 27 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r27_part14 : ∀ i ∈ List.range 1, CorrectAt 27 (112+i) := by
  decide +kernel

theorem base_r27_part14 : ∀ i ∈ List.range 1, BaseCheckAt 27 (112+i) := by
  decide +kernel

theorem strict_r27_part14 : ∀ i ∈ List.range 1, StrictCheckAt 27 (112+i) := by
  have hfast : ∀ i ∈ List.range 1, StrictAtFast (row 27 (112+i)) 27 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 1 := List.mem_range.mp hi
  exact strictAtFast_sound (row 27 (112+i)) 27 (112+i)
    (validAll 27 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
