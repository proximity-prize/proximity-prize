import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r26_part0 : ∀ i ∈ List.range 8, CorrectAt 26 (0+i) := by
  decide +kernel

theorem base_r26_part0 : ∀ i ∈ List.range 8, BaseCheckAt 26 (0+i) := by
  decide +kernel

theorem strict_r26_part0 : ∀ i ∈ List.range 8, StrictCheckAt 26 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (0+i)) 26 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (0+i)) 26 (0+i)
    (validAll 26 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part1 : ∀ i ∈ List.range 8, CorrectAt 26 (8+i) := by
  decide +kernel

theorem base_r26_part1 : ∀ i ∈ List.range 8, BaseCheckAt 26 (8+i) := by
  decide +kernel

theorem strict_r26_part1 : ∀ i ∈ List.range 8, StrictCheckAt 26 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (8+i)) 26 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (8+i)) 26 (8+i)
    (validAll 26 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part2 : ∀ i ∈ List.range 8, CorrectAt 26 (16+i) := by
  decide +kernel

theorem base_r26_part2 : ∀ i ∈ List.range 8, BaseCheckAt 26 (16+i) := by
  decide +kernel

theorem strict_r26_part2 : ∀ i ∈ List.range 8, StrictCheckAt 26 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (16+i)) 26 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (16+i)) 26 (16+i)
    (validAll 26 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part3 : ∀ i ∈ List.range 8, CorrectAt 26 (24+i) := by
  decide +kernel

theorem base_r26_part3 : ∀ i ∈ List.range 8, BaseCheckAt 26 (24+i) := by
  decide +kernel

theorem strict_r26_part3 : ∀ i ∈ List.range 8, StrictCheckAt 26 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (24+i)) 26 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (24+i)) 26 (24+i)
    (validAll 26 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part4 : ∀ i ∈ List.range 8, CorrectAt 26 (32+i) := by
  decide +kernel

theorem base_r26_part4 : ∀ i ∈ List.range 8, BaseCheckAt 26 (32+i) := by
  decide +kernel

theorem strict_r26_part4 : ∀ i ∈ List.range 8, StrictCheckAt 26 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (32+i)) 26 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (32+i)) 26 (32+i)
    (validAll 26 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part5 : ∀ i ∈ List.range 8, CorrectAt 26 (40+i) := by
  decide +kernel

theorem base_r26_part5 : ∀ i ∈ List.range 8, BaseCheckAt 26 (40+i) := by
  decide +kernel

theorem strict_r26_part5 : ∀ i ∈ List.range 8, StrictCheckAt 26 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (40+i)) 26 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (40+i)) 26 (40+i)
    (validAll 26 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part6 : ∀ i ∈ List.range 8, CorrectAt 26 (48+i) := by
  decide +kernel

theorem base_r26_part6 : ∀ i ∈ List.range 8, BaseCheckAt 26 (48+i) := by
  decide +kernel

theorem strict_r26_part6 : ∀ i ∈ List.range 8, StrictCheckAt 26 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (48+i)) 26 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (48+i)) 26 (48+i)
    (validAll 26 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part7 : ∀ i ∈ List.range 8, CorrectAt 26 (56+i) := by
  decide +kernel

theorem base_r26_part7 : ∀ i ∈ List.range 8, BaseCheckAt 26 (56+i) := by
  decide +kernel

theorem strict_r26_part7 : ∀ i ∈ List.range 8, StrictCheckAt 26 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (56+i)) 26 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (56+i)) 26 (56+i)
    (validAll 26 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part8 : ∀ i ∈ List.range 8, CorrectAt 26 (64+i) := by
  decide +kernel

theorem base_r26_part8 : ∀ i ∈ List.range 8, BaseCheckAt 26 (64+i) := by
  decide +kernel

theorem strict_r26_part8 : ∀ i ∈ List.range 8, StrictCheckAt 26 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (64+i)) 26 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (64+i)) 26 (64+i)
    (validAll 26 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part9 : ∀ i ∈ List.range 8, CorrectAt 26 (72+i) := by
  decide +kernel

theorem base_r26_part9 : ∀ i ∈ List.range 8, BaseCheckAt 26 (72+i) := by
  decide +kernel

theorem strict_r26_part9 : ∀ i ∈ List.range 8, StrictCheckAt 26 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (72+i)) 26 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (72+i)) 26 (72+i)
    (validAll 26 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part10 : ∀ i ∈ List.range 8, CorrectAt 26 (80+i) := by
  decide +kernel

theorem base_r26_part10 : ∀ i ∈ List.range 8, BaseCheckAt 26 (80+i) := by
  decide +kernel

theorem strict_r26_part10 : ∀ i ∈ List.range 8, StrictCheckAt 26 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (80+i)) 26 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (80+i)) 26 (80+i)
    (validAll 26 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part11 : ∀ i ∈ List.range 8, CorrectAt 26 (88+i) := by
  decide +kernel

theorem base_r26_part11 : ∀ i ∈ List.range 8, BaseCheckAt 26 (88+i) := by
  decide +kernel

theorem strict_r26_part11 : ∀ i ∈ List.range 8, StrictCheckAt 26 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (88+i)) 26 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (88+i)) 26 (88+i)
    (validAll 26 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part12 : ∀ i ∈ List.range 8, CorrectAt 26 (96+i) := by
  decide +kernel

theorem base_r26_part12 : ∀ i ∈ List.range 8, BaseCheckAt 26 (96+i) := by
  decide +kernel

theorem strict_r26_part12 : ∀ i ∈ List.range 8, StrictCheckAt 26 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (96+i)) 26 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (96+i)) 26 (96+i)
    (validAll 26 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part13 : ∀ i ∈ List.range 8, CorrectAt 26 (104+i) := by
  decide +kernel

theorem base_r26_part13 : ∀ i ∈ List.range 8, BaseCheckAt 26 (104+i) := by
  decide +kernel

theorem strict_r26_part13 : ∀ i ∈ List.range 8, StrictCheckAt 26 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 26 (104+i)) 26 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (104+i)) 26 (104+i)
    (validAll 26 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r26_part14 : ∀ i ∈ List.range 2, CorrectAt 26 (112+i) := by
  decide +kernel

theorem base_r26_part14 : ∀ i ∈ List.range 2, BaseCheckAt 26 (112+i) := by
  decide +kernel

theorem strict_r26_part14 : ∀ i ∈ List.range 2, StrictCheckAt 26 (112+i) := by
  have hfast : ∀ i ∈ List.range 2, StrictAtFast (row 26 (112+i)) 26 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 2 := List.mem_range.mp hi
  exact strictAtFast_sound (row 26 (112+i)) 26 (112+i)
    (validAll 26 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
