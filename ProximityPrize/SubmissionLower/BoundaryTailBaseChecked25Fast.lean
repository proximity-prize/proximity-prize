import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r25_part0 : ∀ i ∈ List.range 8, CorrectAt 25 (0+i) := by
  decide +kernel

theorem base_r25_part0 : ∀ i ∈ List.range 8, BaseCheckAt 25 (0+i) := by
  decide +kernel

theorem strict_r25_part0 : ∀ i ∈ List.range 8, StrictCheckAt 25 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (0+i)) 25 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (0+i)) 25 (0+i)
    (validAll 25 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part1 : ∀ i ∈ List.range 8, CorrectAt 25 (8+i) := by
  decide +kernel

theorem base_r25_part1 : ∀ i ∈ List.range 8, BaseCheckAt 25 (8+i) := by
  decide +kernel

theorem strict_r25_part1 : ∀ i ∈ List.range 8, StrictCheckAt 25 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (8+i)) 25 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (8+i)) 25 (8+i)
    (validAll 25 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part2 : ∀ i ∈ List.range 8, CorrectAt 25 (16+i) := by
  decide +kernel

theorem base_r25_part2 : ∀ i ∈ List.range 8, BaseCheckAt 25 (16+i) := by
  decide +kernel

theorem strict_r25_part2 : ∀ i ∈ List.range 8, StrictCheckAt 25 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (16+i)) 25 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (16+i)) 25 (16+i)
    (validAll 25 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part3 : ∀ i ∈ List.range 8, CorrectAt 25 (24+i) := by
  decide +kernel

theorem base_r25_part3 : ∀ i ∈ List.range 8, BaseCheckAt 25 (24+i) := by
  decide +kernel

theorem strict_r25_part3 : ∀ i ∈ List.range 8, StrictCheckAt 25 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (24+i)) 25 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (24+i)) 25 (24+i)
    (validAll 25 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part4 : ∀ i ∈ List.range 8, CorrectAt 25 (32+i) := by
  decide +kernel

theorem base_r25_part4 : ∀ i ∈ List.range 8, BaseCheckAt 25 (32+i) := by
  decide +kernel

theorem strict_r25_part4 : ∀ i ∈ List.range 8, StrictCheckAt 25 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (32+i)) 25 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (32+i)) 25 (32+i)
    (validAll 25 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part5 : ∀ i ∈ List.range 8, CorrectAt 25 (40+i) := by
  decide +kernel

theorem base_r25_part5 : ∀ i ∈ List.range 8, BaseCheckAt 25 (40+i) := by
  decide +kernel

theorem strict_r25_part5 : ∀ i ∈ List.range 8, StrictCheckAt 25 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (40+i)) 25 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (40+i)) 25 (40+i)
    (validAll 25 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part6 : ∀ i ∈ List.range 8, CorrectAt 25 (48+i) := by
  decide +kernel

theorem base_r25_part6 : ∀ i ∈ List.range 8, BaseCheckAt 25 (48+i) := by
  decide +kernel

theorem strict_r25_part6 : ∀ i ∈ List.range 8, StrictCheckAt 25 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (48+i)) 25 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (48+i)) 25 (48+i)
    (validAll 25 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part7 : ∀ i ∈ List.range 8, CorrectAt 25 (56+i) := by
  decide +kernel

theorem base_r25_part7 : ∀ i ∈ List.range 8, BaseCheckAt 25 (56+i) := by
  decide +kernel

theorem strict_r25_part7 : ∀ i ∈ List.range 8, StrictCheckAt 25 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (56+i)) 25 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (56+i)) 25 (56+i)
    (validAll 25 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part8 : ∀ i ∈ List.range 8, CorrectAt 25 (64+i) := by
  decide +kernel

theorem base_r25_part8 : ∀ i ∈ List.range 8, BaseCheckAt 25 (64+i) := by
  decide +kernel

theorem strict_r25_part8 : ∀ i ∈ List.range 8, StrictCheckAt 25 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (64+i)) 25 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (64+i)) 25 (64+i)
    (validAll 25 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part9 : ∀ i ∈ List.range 8, CorrectAt 25 (72+i) := by
  decide +kernel

theorem base_r25_part9 : ∀ i ∈ List.range 8, BaseCheckAt 25 (72+i) := by
  decide +kernel

theorem strict_r25_part9 : ∀ i ∈ List.range 8, StrictCheckAt 25 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (72+i)) 25 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (72+i)) 25 (72+i)
    (validAll 25 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part10 : ∀ i ∈ List.range 8, CorrectAt 25 (80+i) := by
  decide +kernel

theorem base_r25_part10 : ∀ i ∈ List.range 8, BaseCheckAt 25 (80+i) := by
  decide +kernel

theorem strict_r25_part10 : ∀ i ∈ List.range 8, StrictCheckAt 25 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (80+i)) 25 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (80+i)) 25 (80+i)
    (validAll 25 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part11 : ∀ i ∈ List.range 8, CorrectAt 25 (88+i) := by
  decide +kernel

theorem base_r25_part11 : ∀ i ∈ List.range 8, BaseCheckAt 25 (88+i) := by
  decide +kernel

theorem strict_r25_part11 : ∀ i ∈ List.range 8, StrictCheckAt 25 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (88+i)) 25 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (88+i)) 25 (88+i)
    (validAll 25 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part12 : ∀ i ∈ List.range 8, CorrectAt 25 (96+i) := by
  decide +kernel

theorem base_r25_part12 : ∀ i ∈ List.range 8, BaseCheckAt 25 (96+i) := by
  decide +kernel

theorem strict_r25_part12 : ∀ i ∈ List.range 8, StrictCheckAt 25 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (96+i)) 25 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (96+i)) 25 (96+i)
    (validAll 25 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part13 : ∀ i ∈ List.range 8, CorrectAt 25 (104+i) := by
  decide +kernel

theorem base_r25_part13 : ∀ i ∈ List.range 8, BaseCheckAt 25 (104+i) := by
  decide +kernel

theorem strict_r25_part13 : ∀ i ∈ List.range 8, StrictCheckAt 25 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 25 (104+i)) 25 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (104+i)) 25 (104+i)
    (validAll 25 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r25_part14 : ∀ i ∈ List.range 3, CorrectAt 25 (112+i) := by
  decide +kernel

theorem base_r25_part14 : ∀ i ∈ List.range 3, BaseCheckAt 25 (112+i) := by
  decide +kernel

theorem strict_r25_part14 : ∀ i ∈ List.range 3, StrictCheckAt 25 (112+i) := by
  have hfast : ∀ i ∈ List.range 3, StrictAtFast (row 25 (112+i)) 25 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 3 := List.mem_range.mp hi
  exact strictAtFast_sound (row 25 (112+i)) 25 (112+i)
    (validAll 25 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
