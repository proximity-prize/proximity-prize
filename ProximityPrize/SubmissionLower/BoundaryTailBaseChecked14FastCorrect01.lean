import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r14_part0 : ∀ i ∈ List.range 8, CorrectAt 14 (0+i) := by decide +kernel

theorem correct_r14_part1 : ∀ i ∈ List.range 8, CorrectAt 14 (8+i) := by decide +kernel

theorem correct_r14_part2 : ∀ i ∈ List.range 8, CorrectAt 14 (16+i) := by decide +kernel

theorem correct_r14_part3 : ∀ i ∈ List.range 8, CorrectAt 14 (24+i) := by decide +kernel

theorem correct_r14_part4 : ∀ i ∈ List.range 8, CorrectAt 14 (32+i) := by decide +kernel

theorem correct_r14_part5 : ∀ i ∈ List.range 8, CorrectAt 14 (40+i) := by decide +kernel

theorem correct_r14_part6 : ∀ i ∈ List.range 8, CorrectAt 14 (48+i) := by decide +kernel

theorem correct_r14_part7 : ∀ i ∈ List.range 8, CorrectAt 14 (56+i) := by decide +kernel

theorem correct_r14_part8 : ∀ i ∈ List.range 8, CorrectAt 14 (64+i) := by decide +kernel

theorem correct_r14_part9 : ∀ i ∈ List.range 8, CorrectAt 14 (72+i) := by decide +kernel

theorem correct_r14_part10 : ∀ i ∈ List.range 8, CorrectAt 14 (80+i) := by decide +kernel

theorem correct_r14_part11 : ∀ i ∈ List.range 8, CorrectAt 14 (88+i) := by decide +kernel

theorem correct_r14_part12 : ∀ i ∈ List.range 8, CorrectAt 14 (96+i) := by decide +kernel

theorem correct_r14_part13 : ∀ i ∈ List.range 8, CorrectAt 14 (104+i) := by decide +kernel

theorem correct_r14_part14 : ∀ i ∈ List.range 8, CorrectAt 14 (112+i) := by decide +kernel

theorem correct_r14_part15 : ∀ i ∈ List.range 6, CorrectAt 14 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
