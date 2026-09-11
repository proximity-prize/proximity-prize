import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r24_part0 : ∀ i ∈ List.range 8, CorrectAt 24 (0+i) := by
  decide +kernel

theorem base_r24_part0 : ∀ i ∈ List.range 8, BaseCheckAt 24 (0+i) := by
  decide +kernel

theorem strict_r24_part0 : ∀ i ∈ List.range 8, StrictCheckAt 24 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (0+i)) 24 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (0+i)) 24 (0+i)
    (validAll 24 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part1 : ∀ i ∈ List.range 8, CorrectAt 24 (8+i) := by
  decide +kernel

theorem base_r24_part1 : ∀ i ∈ List.range 8, BaseCheckAt 24 (8+i) := by
  decide +kernel

theorem strict_r24_part1 : ∀ i ∈ List.range 8, StrictCheckAt 24 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (8+i)) 24 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (8+i)) 24 (8+i)
    (validAll 24 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part2 : ∀ i ∈ List.range 8, CorrectAt 24 (16+i) := by
  decide +kernel

theorem base_r24_part2 : ∀ i ∈ List.range 8, BaseCheckAt 24 (16+i) := by
  decide +kernel

theorem strict_r24_part2 : ∀ i ∈ List.range 8, StrictCheckAt 24 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (16+i)) 24 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (16+i)) 24 (16+i)
    (validAll 24 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part3 : ∀ i ∈ List.range 8, CorrectAt 24 (24+i) := by
  decide +kernel

theorem base_r24_part3 : ∀ i ∈ List.range 8, BaseCheckAt 24 (24+i) := by
  decide +kernel

theorem strict_r24_part3 : ∀ i ∈ List.range 8, StrictCheckAt 24 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (24+i)) 24 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (24+i)) 24 (24+i)
    (validAll 24 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part4 : ∀ i ∈ List.range 8, CorrectAt 24 (32+i) := by
  decide +kernel

theorem base_r24_part4 : ∀ i ∈ List.range 8, BaseCheckAt 24 (32+i) := by
  decide +kernel

theorem strict_r24_part4 : ∀ i ∈ List.range 8, StrictCheckAt 24 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (32+i)) 24 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (32+i)) 24 (32+i)
    (validAll 24 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part5 : ∀ i ∈ List.range 8, CorrectAt 24 (40+i) := by
  decide +kernel

theorem base_r24_part5 : ∀ i ∈ List.range 8, BaseCheckAt 24 (40+i) := by
  decide +kernel

theorem strict_r24_part5 : ∀ i ∈ List.range 8, StrictCheckAt 24 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (40+i)) 24 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (40+i)) 24 (40+i)
    (validAll 24 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part6 : ∀ i ∈ List.range 8, CorrectAt 24 (48+i) := by
  decide +kernel

theorem base_r24_part6 : ∀ i ∈ List.range 8, BaseCheckAt 24 (48+i) := by
  decide +kernel

theorem strict_r24_part6 : ∀ i ∈ List.range 8, StrictCheckAt 24 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (48+i)) 24 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (48+i)) 24 (48+i)
    (validAll 24 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part7 : ∀ i ∈ List.range 8, CorrectAt 24 (56+i) := by
  decide +kernel

theorem base_r24_part7 : ∀ i ∈ List.range 8, BaseCheckAt 24 (56+i) := by
  decide +kernel

theorem strict_r24_part7 : ∀ i ∈ List.range 8, StrictCheckAt 24 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (56+i)) 24 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (56+i)) 24 (56+i)
    (validAll 24 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part8 : ∀ i ∈ List.range 8, CorrectAt 24 (64+i) := by
  decide +kernel

theorem base_r24_part8 : ∀ i ∈ List.range 8, BaseCheckAt 24 (64+i) := by
  decide +kernel

theorem strict_r24_part8 : ∀ i ∈ List.range 8, StrictCheckAt 24 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (64+i)) 24 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (64+i)) 24 (64+i)
    (validAll 24 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part9 : ∀ i ∈ List.range 8, CorrectAt 24 (72+i) := by
  decide +kernel

theorem base_r24_part9 : ∀ i ∈ List.range 8, BaseCheckAt 24 (72+i) := by
  decide +kernel

theorem strict_r24_part9 : ∀ i ∈ List.range 8, StrictCheckAt 24 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (72+i)) 24 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (72+i)) 24 (72+i)
    (validAll 24 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part10 : ∀ i ∈ List.range 8, CorrectAt 24 (80+i) := by
  decide +kernel

theorem base_r24_part10 : ∀ i ∈ List.range 8, BaseCheckAt 24 (80+i) := by
  decide +kernel

theorem strict_r24_part10 : ∀ i ∈ List.range 8, StrictCheckAt 24 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (80+i)) 24 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (80+i)) 24 (80+i)
    (validAll 24 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part11 : ∀ i ∈ List.range 8, CorrectAt 24 (88+i) := by
  decide +kernel

theorem base_r24_part11 : ∀ i ∈ List.range 8, BaseCheckAt 24 (88+i) := by
  decide +kernel

theorem strict_r24_part11 : ∀ i ∈ List.range 8, StrictCheckAt 24 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (88+i)) 24 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (88+i)) 24 (88+i)
    (validAll 24 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part12 : ∀ i ∈ List.range 8, CorrectAt 24 (96+i) := by
  decide +kernel

theorem base_r24_part12 : ∀ i ∈ List.range 8, BaseCheckAt 24 (96+i) := by
  decide +kernel

theorem strict_r24_part12 : ∀ i ∈ List.range 8, StrictCheckAt 24 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (96+i)) 24 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (96+i)) 24 (96+i)
    (validAll 24 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part13 : ∀ i ∈ List.range 8, CorrectAt 24 (104+i) := by
  decide +kernel

theorem base_r24_part13 : ∀ i ∈ List.range 8, BaseCheckAt 24 (104+i) := by
  decide +kernel

theorem strict_r24_part13 : ∀ i ∈ List.range 8, StrictCheckAt 24 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 24 (104+i)) 24 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (104+i)) 24 (104+i)
    (validAll 24 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r24_part14 : ∀ i ∈ List.range 4, CorrectAt 24 (112+i) := by
  decide +kernel

theorem base_r24_part14 : ∀ i ∈ List.range 4, BaseCheckAt 24 (112+i) := by
  decide +kernel

theorem strict_r24_part14 : ∀ i ∈ List.range 4, StrictCheckAt 24 (112+i) := by
  have hfast : ∀ i ∈ List.range 4, StrictAtFast (row 24 (112+i)) 24 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 4 := List.mem_range.mp hi
  exact strictAtFast_sound (row 24 (112+i)) 24 (112+i)
    (validAll 24 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
