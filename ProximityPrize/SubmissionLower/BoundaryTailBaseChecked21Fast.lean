import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r21_part0 : ∀ i ∈ List.range 8, CorrectAt 21 (0+i) := by
  decide +kernel

theorem base_r21_part0 : ∀ i ∈ List.range 8, BaseCheckAt 21 (0+i) := by
  decide +kernel

theorem strict_r21_part0 : ∀ i ∈ List.range 8, StrictCheckAt 21 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (0+i)) 21 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (0+i)) 21 (0+i)
    (validAll 21 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part1 : ∀ i ∈ List.range 8, CorrectAt 21 (8+i) := by
  decide +kernel

theorem base_r21_part1 : ∀ i ∈ List.range 8, BaseCheckAt 21 (8+i) := by
  decide +kernel

theorem strict_r21_part1 : ∀ i ∈ List.range 8, StrictCheckAt 21 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (8+i)) 21 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (8+i)) 21 (8+i)
    (validAll 21 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part2 : ∀ i ∈ List.range 8, CorrectAt 21 (16+i) := by
  decide +kernel

theorem base_r21_part2 : ∀ i ∈ List.range 8, BaseCheckAt 21 (16+i) := by
  decide +kernel

theorem strict_r21_part2 : ∀ i ∈ List.range 8, StrictCheckAt 21 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (16+i)) 21 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (16+i)) 21 (16+i)
    (validAll 21 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part3 : ∀ i ∈ List.range 8, CorrectAt 21 (24+i) := by
  decide +kernel

theorem base_r21_part3 : ∀ i ∈ List.range 8, BaseCheckAt 21 (24+i) := by
  decide +kernel

theorem strict_r21_part3 : ∀ i ∈ List.range 8, StrictCheckAt 21 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (24+i)) 21 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (24+i)) 21 (24+i)
    (validAll 21 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part4 : ∀ i ∈ List.range 8, CorrectAt 21 (32+i) := by
  decide +kernel

theorem base_r21_part4 : ∀ i ∈ List.range 8, BaseCheckAt 21 (32+i) := by
  decide +kernel

theorem strict_r21_part4 : ∀ i ∈ List.range 8, StrictCheckAt 21 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (32+i)) 21 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (32+i)) 21 (32+i)
    (validAll 21 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part5 : ∀ i ∈ List.range 8, CorrectAt 21 (40+i) := by
  decide +kernel

theorem base_r21_part5 : ∀ i ∈ List.range 8, BaseCheckAt 21 (40+i) := by
  decide +kernel

theorem strict_r21_part5 : ∀ i ∈ List.range 8, StrictCheckAt 21 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (40+i)) 21 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (40+i)) 21 (40+i)
    (validAll 21 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part6 : ∀ i ∈ List.range 8, CorrectAt 21 (48+i) := by
  decide +kernel

theorem base_r21_part6 : ∀ i ∈ List.range 8, BaseCheckAt 21 (48+i) := by
  decide +kernel

theorem strict_r21_part6 : ∀ i ∈ List.range 8, StrictCheckAt 21 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (48+i)) 21 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (48+i)) 21 (48+i)
    (validAll 21 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part7 : ∀ i ∈ List.range 8, CorrectAt 21 (56+i) := by
  decide +kernel

theorem base_r21_part7 : ∀ i ∈ List.range 8, BaseCheckAt 21 (56+i) := by
  decide +kernel

theorem strict_r21_part7 : ∀ i ∈ List.range 8, StrictCheckAt 21 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (56+i)) 21 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (56+i)) 21 (56+i)
    (validAll 21 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part8 : ∀ i ∈ List.range 8, CorrectAt 21 (64+i) := by
  decide +kernel

theorem base_r21_part8 : ∀ i ∈ List.range 8, BaseCheckAt 21 (64+i) := by
  decide +kernel

theorem strict_r21_part8 : ∀ i ∈ List.range 8, StrictCheckAt 21 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (64+i)) 21 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (64+i)) 21 (64+i)
    (validAll 21 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part9 : ∀ i ∈ List.range 8, CorrectAt 21 (72+i) := by
  decide +kernel

theorem base_r21_part9 : ∀ i ∈ List.range 8, BaseCheckAt 21 (72+i) := by
  decide +kernel

theorem strict_r21_part9 : ∀ i ∈ List.range 8, StrictCheckAt 21 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (72+i)) 21 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (72+i)) 21 (72+i)
    (validAll 21 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part10 : ∀ i ∈ List.range 8, CorrectAt 21 (80+i) := by
  decide +kernel

theorem base_r21_part10 : ∀ i ∈ List.range 8, BaseCheckAt 21 (80+i) := by
  decide +kernel

theorem strict_r21_part10 : ∀ i ∈ List.range 8, StrictCheckAt 21 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (80+i)) 21 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (80+i)) 21 (80+i)
    (validAll 21 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part11 : ∀ i ∈ List.range 8, CorrectAt 21 (88+i) := by
  decide +kernel

theorem base_r21_part11 : ∀ i ∈ List.range 8, BaseCheckAt 21 (88+i) := by
  decide +kernel

theorem strict_r21_part11 : ∀ i ∈ List.range 8, StrictCheckAt 21 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (88+i)) 21 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (88+i)) 21 (88+i)
    (validAll 21 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part12 : ∀ i ∈ List.range 8, CorrectAt 21 (96+i) := by
  decide +kernel

theorem base_r21_part12 : ∀ i ∈ List.range 8, BaseCheckAt 21 (96+i) := by
  decide +kernel

theorem strict_r21_part12 : ∀ i ∈ List.range 8, StrictCheckAt 21 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (96+i)) 21 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (96+i)) 21 (96+i)
    (validAll 21 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part13 : ∀ i ∈ List.range 8, CorrectAt 21 (104+i) := by
  decide +kernel

theorem base_r21_part13 : ∀ i ∈ List.range 8, BaseCheckAt 21 (104+i) := by
  decide +kernel

theorem strict_r21_part13 : ∀ i ∈ List.range 8, StrictCheckAt 21 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 21 (104+i)) 21 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (104+i)) 21 (104+i)
    (validAll 21 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r21_part14 : ∀ i ∈ List.range 7, CorrectAt 21 (112+i) := by
  decide +kernel

theorem base_r21_part14 : ∀ i ∈ List.range 7, BaseCheckAt 21 (112+i) := by
  decide +kernel

theorem strict_r21_part14 : ∀ i ∈ List.range 7, StrictCheckAt 21 (112+i) := by
  have hfast : ∀ i ∈ List.range 7, StrictAtFast (row 21 (112+i)) 21 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 7 := List.mem_range.mp hi
  exact strictAtFast_sound (row 21 (112+i)) 21 (112+i)
    (validAll 21 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
