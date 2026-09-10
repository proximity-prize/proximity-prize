import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r19_part0 : ∀ i ∈ List.range 8, CorrectAt 19 (0+i) := by decide +kernel

theorem correct_r19_part1 : ∀ i ∈ List.range 8, CorrectAt 19 (8+i) := by decide +kernel

theorem correct_r19_part2 : ∀ i ∈ List.range 8, CorrectAt 19 (16+i) := by decide +kernel

theorem correct_r19_part3 : ∀ i ∈ List.range 8, CorrectAt 19 (24+i) := by decide +kernel

theorem correct_r19_part4 : ∀ i ∈ List.range 8, CorrectAt 19 (32+i) := by decide +kernel

theorem correct_r19_part5 : ∀ i ∈ List.range 8, CorrectAt 19 (40+i) := by decide +kernel

theorem correct_r19_part6 : ∀ i ∈ List.range 8, CorrectAt 19 (48+i) := by decide +kernel

theorem correct_r19_part7 : ∀ i ∈ List.range 8, CorrectAt 19 (56+i) := by decide +kernel

theorem correct_r19_part8 : ∀ i ∈ List.range 8, CorrectAt 19 (64+i) := by decide +kernel

theorem correct_r19_part9 : ∀ i ∈ List.range 8, CorrectAt 19 (72+i) := by decide +kernel

theorem correct_r19_part10 : ∀ i ∈ List.range 8, CorrectAt 19 (80+i) := by decide +kernel

theorem correct_r19_part11 : ∀ i ∈ List.range 8, CorrectAt 19 (88+i) := by decide +kernel

theorem correct_r19_part12 : ∀ i ∈ List.range 8, CorrectAt 19 (96+i) := by decide +kernel

theorem correct_r19_part13 : ∀ i ∈ List.range 8, CorrectAt 19 (104+i) := by decide +kernel

theorem correct_r19_part14 : ∀ i ∈ List.range 8, CorrectAt 19 (112+i) := by decide +kernel

theorem correct_r19_part15 : ∀ i ∈ List.range 1, CorrectAt 19 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
