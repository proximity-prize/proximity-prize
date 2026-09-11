import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r20_part0 : ∀ i ∈ List.range 8, CorrectAt 20 (0+i) := by
  decide +kernel

theorem base_r20_part0 : ∀ i ∈ List.range 8, BaseCheckAt 20 (0+i) := by
  decide +kernel

theorem strict_r20_part0 : ∀ i ∈ List.range 8, StrictCheckAt 20 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (0+i)) 20 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (0+i)) 20 (0+i)
    (validAll 20 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part1 : ∀ i ∈ List.range 8, CorrectAt 20 (8+i) := by
  decide +kernel

theorem base_r20_part1 : ∀ i ∈ List.range 8, BaseCheckAt 20 (8+i) := by
  decide +kernel

theorem strict_r20_part1 : ∀ i ∈ List.range 8, StrictCheckAt 20 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (8+i)) 20 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (8+i)) 20 (8+i)
    (validAll 20 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part2 : ∀ i ∈ List.range 8, CorrectAt 20 (16+i) := by
  decide +kernel

theorem base_r20_part2 : ∀ i ∈ List.range 8, BaseCheckAt 20 (16+i) := by
  decide +kernel

theorem strict_r20_part2 : ∀ i ∈ List.range 8, StrictCheckAt 20 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (16+i)) 20 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (16+i)) 20 (16+i)
    (validAll 20 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part3 : ∀ i ∈ List.range 8, CorrectAt 20 (24+i) := by
  decide +kernel

theorem base_r20_part3 : ∀ i ∈ List.range 8, BaseCheckAt 20 (24+i) := by
  decide +kernel

theorem strict_r20_part3 : ∀ i ∈ List.range 8, StrictCheckAt 20 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (24+i)) 20 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (24+i)) 20 (24+i)
    (validAll 20 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part4 : ∀ i ∈ List.range 8, CorrectAt 20 (32+i) := by
  decide +kernel

theorem base_r20_part4 : ∀ i ∈ List.range 8, BaseCheckAt 20 (32+i) := by
  decide +kernel

theorem strict_r20_part4 : ∀ i ∈ List.range 8, StrictCheckAt 20 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (32+i)) 20 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (32+i)) 20 (32+i)
    (validAll 20 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part5 : ∀ i ∈ List.range 8, CorrectAt 20 (40+i) := by
  decide +kernel

theorem base_r20_part5 : ∀ i ∈ List.range 8, BaseCheckAt 20 (40+i) := by
  decide +kernel

theorem strict_r20_part5 : ∀ i ∈ List.range 8, StrictCheckAt 20 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (40+i)) 20 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (40+i)) 20 (40+i)
    (validAll 20 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part6 : ∀ i ∈ List.range 8, CorrectAt 20 (48+i) := by
  decide +kernel

theorem base_r20_part6 : ∀ i ∈ List.range 8, BaseCheckAt 20 (48+i) := by
  decide +kernel

theorem strict_r20_part6 : ∀ i ∈ List.range 8, StrictCheckAt 20 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (48+i)) 20 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (48+i)) 20 (48+i)
    (validAll 20 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part7 : ∀ i ∈ List.range 8, CorrectAt 20 (56+i) := by
  decide +kernel

theorem base_r20_part7 : ∀ i ∈ List.range 8, BaseCheckAt 20 (56+i) := by
  decide +kernel

theorem strict_r20_part7 : ∀ i ∈ List.range 8, StrictCheckAt 20 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (56+i)) 20 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (56+i)) 20 (56+i)
    (validAll 20 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part8 : ∀ i ∈ List.range 8, CorrectAt 20 (64+i) := by
  decide +kernel

theorem base_r20_part8 : ∀ i ∈ List.range 8, BaseCheckAt 20 (64+i) := by
  decide +kernel

theorem strict_r20_part8 : ∀ i ∈ List.range 8, StrictCheckAt 20 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (64+i)) 20 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (64+i)) 20 (64+i)
    (validAll 20 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part9 : ∀ i ∈ List.range 8, CorrectAt 20 (72+i) := by
  decide +kernel

theorem base_r20_part9 : ∀ i ∈ List.range 8, BaseCheckAt 20 (72+i) := by
  decide +kernel

theorem strict_r20_part9 : ∀ i ∈ List.range 8, StrictCheckAt 20 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (72+i)) 20 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (72+i)) 20 (72+i)
    (validAll 20 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part10 : ∀ i ∈ List.range 8, CorrectAt 20 (80+i) := by
  decide +kernel

theorem base_r20_part10 : ∀ i ∈ List.range 8, BaseCheckAt 20 (80+i) := by
  decide +kernel

theorem strict_r20_part10 : ∀ i ∈ List.range 8, StrictCheckAt 20 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (80+i)) 20 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (80+i)) 20 (80+i)
    (validAll 20 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part11 : ∀ i ∈ List.range 8, CorrectAt 20 (88+i) := by
  decide +kernel

theorem base_r20_part11 : ∀ i ∈ List.range 8, BaseCheckAt 20 (88+i) := by
  decide +kernel

theorem strict_r20_part11 : ∀ i ∈ List.range 8, StrictCheckAt 20 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (88+i)) 20 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (88+i)) 20 (88+i)
    (validAll 20 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part12 : ∀ i ∈ List.range 8, CorrectAt 20 (96+i) := by
  decide +kernel

theorem base_r20_part12 : ∀ i ∈ List.range 8, BaseCheckAt 20 (96+i) := by
  decide +kernel

theorem strict_r20_part12 : ∀ i ∈ List.range 8, StrictCheckAt 20 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (96+i)) 20 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (96+i)) 20 (96+i)
    (validAll 20 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part13 : ∀ i ∈ List.range 8, CorrectAt 20 (104+i) := by
  decide +kernel

theorem base_r20_part13 : ∀ i ∈ List.range 8, BaseCheckAt 20 (104+i) := by
  decide +kernel

theorem strict_r20_part13 : ∀ i ∈ List.range 8, StrictCheckAt 20 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (104+i)) 20 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (104+i)) 20 (104+i)
    (validAll 20 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r20_part14 : ∀ i ∈ List.range 8, CorrectAt 20 (112+i) := by
  decide +kernel

theorem base_r20_part14 : ∀ i ∈ List.range 8, BaseCheckAt 20 (112+i) := by
  decide +kernel

theorem strict_r20_part14 : ∀ i ∈ List.range 8, StrictCheckAt 20 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 20 (112+i)) 20 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 20 (112+i)) 20 (112+i)
    (validAll 20 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
