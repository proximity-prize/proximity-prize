import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11
import ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open ProximityPrize.SubmissionLower.BoundaryTailZeroFromAlgebra
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r12_part0 : ∀ i ∈ List.range 8, CorrectAt 12 (0+i) := by
  decide +kernel

theorem base_r12_part0 : ∀ i ∈ List.range 8, BaseCheckAt 12 (0+i) := by
  decide +kernel

theorem strict_r12_part0 : ∀ i ∈ List.range 8, StrictCheckAt 12 (0+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (0+i)) 12 (0+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (0+i)) 12 (0+i)
    (validAll 12 (0+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part1 : ∀ i ∈ List.range 8, CorrectAt 12 (8+i) := by
  decide +kernel

theorem base_r12_part1 : ∀ i ∈ List.range 8, BaseCheckAt 12 (8+i) := by
  decide +kernel

theorem strict_r12_part1 : ∀ i ∈ List.range 8, StrictCheckAt 12 (8+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (8+i)) 12 (8+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (8+i)) 12 (8+i)
    (validAll 12 (8+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part2 : ∀ i ∈ List.range 8, CorrectAt 12 (16+i) := by
  decide +kernel

theorem base_r12_part2 : ∀ i ∈ List.range 8, BaseCheckAt 12 (16+i) := by
  decide +kernel

theorem strict_r12_part2 : ∀ i ∈ List.range 8, StrictCheckAt 12 (16+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (16+i)) 12 (16+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (16+i)) 12 (16+i)
    (validAll 12 (16+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part3 : ∀ i ∈ List.range 8, CorrectAt 12 (24+i) := by
  decide +kernel

theorem base_r12_part3 : ∀ i ∈ List.range 8, BaseCheckAt 12 (24+i) := by
  decide +kernel

theorem strict_r12_part3 : ∀ i ∈ List.range 8, StrictCheckAt 12 (24+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (24+i)) 12 (24+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (24+i)) 12 (24+i)
    (validAll 12 (24+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part4 : ∀ i ∈ List.range 8, CorrectAt 12 (32+i) := by
  decide +kernel

theorem base_r12_part4 : ∀ i ∈ List.range 8, BaseCheckAt 12 (32+i) := by
  decide +kernel

theorem strict_r12_part4 : ∀ i ∈ List.range 8, StrictCheckAt 12 (32+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (32+i)) 12 (32+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (32+i)) 12 (32+i)
    (validAll 12 (32+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part5 : ∀ i ∈ List.range 8, CorrectAt 12 (40+i) := by
  decide +kernel

theorem base_r12_part5 : ∀ i ∈ List.range 8, BaseCheckAt 12 (40+i) := by
  decide +kernel

theorem strict_r12_part5 : ∀ i ∈ List.range 8, StrictCheckAt 12 (40+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (40+i)) 12 (40+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (40+i)) 12 (40+i)
    (validAll 12 (40+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part6 : ∀ i ∈ List.range 8, CorrectAt 12 (48+i) := by
  decide +kernel

theorem base_r12_part6 : ∀ i ∈ List.range 8, BaseCheckAt 12 (48+i) := by
  decide +kernel

theorem strict_r12_part6 : ∀ i ∈ List.range 8, StrictCheckAt 12 (48+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (48+i)) 12 (48+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (48+i)) 12 (48+i)
    (validAll 12 (48+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part7 : ∀ i ∈ List.range 8, CorrectAt 12 (56+i) := by
  decide +kernel

theorem base_r12_part7 : ∀ i ∈ List.range 8, BaseCheckAt 12 (56+i) := by
  decide +kernel

theorem strict_r12_part7 : ∀ i ∈ List.range 8, StrictCheckAt 12 (56+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (56+i)) 12 (56+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (56+i)) 12 (56+i)
    (validAll 12 (56+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part8 : ∀ i ∈ List.range 8, CorrectAt 12 (64+i) := by
  decide +kernel

theorem base_r12_part8 : ∀ i ∈ List.range 8, BaseCheckAt 12 (64+i) := by
  decide +kernel

theorem strict_r12_part8 : ∀ i ∈ List.range 8, StrictCheckAt 12 (64+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (64+i)) 12 (64+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (64+i)) 12 (64+i)
    (validAll 12 (64+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part9 : ∀ i ∈ List.range 8, CorrectAt 12 (72+i) := by
  decide +kernel

theorem base_r12_part9 : ∀ i ∈ List.range 8, BaseCheckAt 12 (72+i) := by
  decide +kernel

theorem strict_r12_part9 : ∀ i ∈ List.range 8, StrictCheckAt 12 (72+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (72+i)) 12 (72+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (72+i)) 12 (72+i)
    (validAll 12 (72+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part10 : ∀ i ∈ List.range 8, CorrectAt 12 (80+i) := by
  decide +kernel

theorem base_r12_part10 : ∀ i ∈ List.range 8, BaseCheckAt 12 (80+i) := by
  decide +kernel

theorem strict_r12_part10 : ∀ i ∈ List.range 8, StrictCheckAt 12 (80+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (80+i)) 12 (80+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (80+i)) 12 (80+i)
    (validAll 12 (80+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part11 : ∀ i ∈ List.range 8, CorrectAt 12 (88+i) := by
  decide +kernel

theorem base_r12_part11 : ∀ i ∈ List.range 8, BaseCheckAt 12 (88+i) := by
  decide +kernel

theorem strict_r12_part11 : ∀ i ∈ List.range 8, StrictCheckAt 12 (88+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (88+i)) 12 (88+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (88+i)) 12 (88+i)
    (validAll 12 (88+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part12 : ∀ i ∈ List.range 8, CorrectAt 12 (96+i) := by
  decide +kernel

theorem base_r12_part12 : ∀ i ∈ List.range 8, BaseCheckAt 12 (96+i) := by
  decide +kernel

theorem strict_r12_part12 : ∀ i ∈ List.range 8, StrictCheckAt 12 (96+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (96+i)) 12 (96+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (96+i)) 12 (96+i)
    (validAll 12 (96+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part13 : ∀ i ∈ List.range 8, CorrectAt 12 (104+i) := by
  decide +kernel

theorem base_r12_part13 : ∀ i ∈ List.range 8, BaseCheckAt 12 (104+i) := by
  decide +kernel

theorem strict_r12_part13 : ∀ i ∈ List.range 8, StrictCheckAt 12 (104+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (104+i)) 12 (104+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (104+i)) 12 (104+i)
    (validAll 12 (104+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part14 : ∀ i ∈ List.range 8, CorrectAt 12 (112+i) := by
  decide +kernel

theorem base_r12_part14 : ∀ i ∈ List.range 8, BaseCheckAt 12 (112+i) := by
  decide +kernel

theorem strict_r12_part14 : ∀ i ∈ List.range 8, StrictCheckAt 12 (112+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (112+i)) 12 (112+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (112+i)) 12 (112+i)
    (validAll 12 (112+i) (by omega) (by omega) (by omega)) (hfast i hi)

theorem correct_r12_part15 : ∀ i ∈ List.range 8, CorrectAt 12 (120+i) := by
  decide +kernel

theorem base_r12_part15 : ∀ i ∈ List.range 8, BaseCheckAt 12 (120+i) := by
  decide +kernel

theorem strict_r12_part15 : ∀ i ∈ List.range 8, StrictCheckAt 12 (120+i) := by
  have hfast : ∀ i ∈ List.range 8, StrictAtFast (row 12 (120+i)) 12 (120+i) := by
    decide +kernel
  intro i hi
  have hi' : i < 8 := List.mem_range.mp hi
  exact strictAtFast_sound (row 12 (120+i)) 12 (120+i)
    (validAll 12 (120+i) (by omega) (by omega) (by omega)) (hfast i hi)

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
