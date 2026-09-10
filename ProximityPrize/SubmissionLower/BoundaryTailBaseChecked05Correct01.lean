import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r5_part0 : ∀ i ∈ List.range 8, CorrectAt 5 (0+i) := by decide +kernel

theorem correct_r5_part1 : ∀ i ∈ List.range 8, CorrectAt 5 (8+i) := by decide +kernel

theorem correct_r5_part2 : ∀ i ∈ List.range 8, CorrectAt 5 (16+i) := by decide +kernel

theorem correct_r5_part3 : ∀ i ∈ List.range 8, CorrectAt 5 (24+i) := by decide +kernel

theorem correct_r5_part4 : ∀ i ∈ List.range 8, CorrectAt 5 (32+i) := by decide +kernel

theorem correct_r5_part5 : ∀ i ∈ List.range 8, CorrectAt 5 (40+i) := by decide +kernel

theorem correct_r5_part6 : ∀ i ∈ List.range 8, CorrectAt 5 (48+i) := by decide +kernel

theorem correct_r5_part7 : ∀ i ∈ List.range 8, CorrectAt 5 (56+i) := by decide +kernel

theorem correct_r5_part8 : ∀ i ∈ List.range 8, CorrectAt 5 (64+i) := by decide +kernel

theorem correct_r5_part9 : ∀ i ∈ List.range 8, CorrectAt 5 (72+i) := by decide +kernel

theorem correct_r5_part10 : ∀ i ∈ List.range 8, CorrectAt 5 (80+i) := by decide +kernel

theorem correct_r5_part11 : ∀ i ∈ List.range 8, CorrectAt 5 (88+i) := by decide +kernel

theorem correct_r5_part12 : ∀ i ∈ List.range 8, CorrectAt 5 (96+i) := by decide +kernel

theorem correct_r5_part13 : ∀ i ∈ List.range 8, CorrectAt 5 (104+i) := by decide +kernel

theorem correct_r5_part14 : ∀ i ∈ List.range 8, CorrectAt 5 (112+i) := by decide +kernel

theorem correct_r5_part15 : ∀ i ∈ List.range 8, CorrectAt 5 (120+i) := by decide +kernel

theorem correct_r5_part16 : ∀ i ∈ List.range 7, CorrectAt 5 (128+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
