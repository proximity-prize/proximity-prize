import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r22_part0 : ∀ i ∈ List.range 8, CorrectAt 22 (0+i) := by
  decide +kernel

theorem base_r22_part0 : ∀ i ∈ List.range 8, BaseCheckAt 22 (0+i) := by
  decide +kernel

theorem strict_r22_part0 : ∀ i ∈ List.range 8, StrictCheckAt 22 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (0+i)) 22 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (0+i)) 22 (0+i)
    (validAll 22 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part1 : ∀ i ∈ List.range 8, CorrectAt 22 (8+i) := by
  decide +kernel

theorem base_r22_part1 : ∀ i ∈ List.range 8, BaseCheckAt 22 (8+i) := by
  decide +kernel

theorem strict_r22_part1 : ∀ i ∈ List.range 8, StrictCheckAt 22 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (8+i)) 22 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (8+i)) 22 (8+i)
    (validAll 22 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part2 : ∀ i ∈ List.range 8, CorrectAt 22 (16+i) := by
  decide +kernel

theorem base_r22_part2 : ∀ i ∈ List.range 8, BaseCheckAt 22 (16+i) := by
  decide +kernel

theorem strict_r22_part2 : ∀ i ∈ List.range 8, StrictCheckAt 22 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (16+i)) 22 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (16+i)) 22 (16+i)
    (validAll 22 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part3 : ∀ i ∈ List.range 8, CorrectAt 22 (24+i) := by
  decide +kernel

theorem base_r22_part3 : ∀ i ∈ List.range 8, BaseCheckAt 22 (24+i) := by
  decide +kernel

theorem strict_r22_part3 : ∀ i ∈ List.range 8, StrictCheckAt 22 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (24+i)) 22 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (24+i)) 22 (24+i)
    (validAll 22 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part4 : ∀ i ∈ List.range 8, CorrectAt 22 (32+i) := by
  decide +kernel

theorem base_r22_part4 : ∀ i ∈ List.range 8, BaseCheckAt 22 (32+i) := by
  decide +kernel

theorem strict_r22_part4 : ∀ i ∈ List.range 8, StrictCheckAt 22 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (32+i)) 22 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (32+i)) 22 (32+i)
    (validAll 22 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part5 : ∀ i ∈ List.range 8, CorrectAt 22 (40+i) := by
  decide +kernel

theorem base_r22_part5 : ∀ i ∈ List.range 8, BaseCheckAt 22 (40+i) := by
  decide +kernel

theorem strict_r22_part5 : ∀ i ∈ List.range 8, StrictCheckAt 22 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (40+i)) 22 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (40+i)) 22 (40+i)
    (validAll 22 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part6 : ∀ i ∈ List.range 8, CorrectAt 22 (48+i) := by
  decide +kernel

theorem base_r22_part6 : ∀ i ∈ List.range 8, BaseCheckAt 22 (48+i) := by
  decide +kernel

theorem strict_r22_part6 : ∀ i ∈ List.range 8, StrictCheckAt 22 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (48+i)) 22 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (48+i)) 22 (48+i)
    (validAll 22 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part7 : ∀ i ∈ List.range 8, CorrectAt 22 (56+i) := by
  decide +kernel

theorem base_r22_part7 : ∀ i ∈ List.range 8, BaseCheckAt 22 (56+i) := by
  decide +kernel

theorem strict_r22_part7 : ∀ i ∈ List.range 8, StrictCheckAt 22 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (56+i)) 22 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (56+i)) 22 (56+i)
    (validAll 22 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part8 : ∀ i ∈ List.range 8, CorrectAt 22 (64+i) := by
  decide +kernel

theorem base_r22_part8 : ∀ i ∈ List.range 8, BaseCheckAt 22 (64+i) := by
  decide +kernel

theorem strict_r22_part8 : ∀ i ∈ List.range 8, StrictCheckAt 22 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (64+i)) 22 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (64+i)) 22 (64+i)
    (validAll 22 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part9 : ∀ i ∈ List.range 8, CorrectAt 22 (72+i) := by
  decide +kernel

theorem base_r22_part9 : ∀ i ∈ List.range 8, BaseCheckAt 22 (72+i) := by
  decide +kernel

theorem strict_r22_part9 : ∀ i ∈ List.range 8, StrictCheckAt 22 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (72+i)) 22 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (72+i)) 22 (72+i)
    (validAll 22 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part10 : ∀ i ∈ List.range 8, CorrectAt 22 (80+i) := by
  decide +kernel

theorem base_r22_part10 : ∀ i ∈ List.range 8, BaseCheckAt 22 (80+i) := by
  decide +kernel

theorem strict_r22_part10 : ∀ i ∈ List.range 8, StrictCheckAt 22 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (80+i)) 22 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (80+i)) 22 (80+i)
    (validAll 22 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part11 : ∀ i ∈ List.range 8, CorrectAt 22 (88+i) := by
  decide +kernel

theorem base_r22_part11 : ∀ i ∈ List.range 8, BaseCheckAt 22 (88+i) := by
  decide +kernel

theorem strict_r22_part11 : ∀ i ∈ List.range 8, StrictCheckAt 22 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (88+i)) 22 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (88+i)) 22 (88+i)
    (validAll 22 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part12 : ∀ i ∈ List.range 8, CorrectAt 22 (96+i) := by
  decide +kernel

theorem base_r22_part12 : ∀ i ∈ List.range 8, BaseCheckAt 22 (96+i) := by
  decide +kernel

theorem strict_r22_part12 : ∀ i ∈ List.range 8, StrictCheckAt 22 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (96+i)) 22 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (96+i)) 22 (96+i)
    (validAll 22 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part13 : ∀ i ∈ List.range 8, CorrectAt 22 (104+i) := by
  decide +kernel

theorem base_r22_part13 : ∀ i ∈ List.range 8, BaseCheckAt 22 (104+i) := by
  decide +kernel

theorem strict_r22_part13 : ∀ i ∈ List.range 8, StrictCheckAt 22 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 22 (104+i)) 22 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (104+i)) 22 (104+i)
    (validAll 22 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r22_part14 : ∀ i ∈ List.range 6, CorrectAt 22 (112+i) := by
  decide +kernel

theorem base_r22_part14 : ∀ i ∈ List.range 6, BaseCheckAt 22 (112+i) := by
  decide +kernel

theorem strict_r22_part14 : ∀ i ∈ List.range 6, StrictCheckAt 22 (112+i) := by
  have hfast : ∀ i ∈ List.range 6, StrictAtFast (row 22 (112+i)) 22 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 6 := List.mem_range.mp hi
  exact strictAtFast_sound (row 22 (112+i)) 22 (112+i)
    (validAll 22 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
