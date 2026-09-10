import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r16_part0 : ∀ i ∈ List.range 8, CorrectAt 16 (0+i) := by decide +kernel

theorem correct_r16_part1 : ∀ i ∈ List.range 8, CorrectAt 16 (8+i) := by decide +kernel

theorem correct_r16_part2 : ∀ i ∈ List.range 8, CorrectAt 16 (16+i) := by decide +kernel

theorem correct_r16_part3 : ∀ i ∈ List.range 8, CorrectAt 16 (24+i) := by decide +kernel

theorem correct_r16_part4 : ∀ i ∈ List.range 8, CorrectAt 16 (32+i) := by decide +kernel

theorem correct_r16_part5 : ∀ i ∈ List.range 8, CorrectAt 16 (40+i) := by decide +kernel

theorem correct_r16_part6 : ∀ i ∈ List.range 8, CorrectAt 16 (48+i) := by decide +kernel

theorem correct_r16_part7 : ∀ i ∈ List.range 8, CorrectAt 16 (56+i) := by decide +kernel

theorem correct_r16_part8 : ∀ i ∈ List.range 8, CorrectAt 16 (64+i) := by decide +kernel

theorem correct_r16_part9 : ∀ i ∈ List.range 8, CorrectAt 16 (72+i) := by decide +kernel

theorem correct_r16_part10 : ∀ i ∈ List.range 8, CorrectAt 16 (80+i) := by decide +kernel

theorem correct_r16_part11 : ∀ i ∈ List.range 8, CorrectAt 16 (88+i) := by decide +kernel

theorem correct_r16_part12 : ∀ i ∈ List.range 8, CorrectAt 16 (96+i) := by decide +kernel

theorem correct_r16_part13 : ∀ i ∈ List.range 8, CorrectAt 16 (104+i) := by decide +kernel

theorem correct_r16_part14 : ∀ i ∈ List.range 8, CorrectAt 16 (112+i) := by decide +kernel

theorem correct_r16_part15 : ∀ i ∈ List.range 4, CorrectAt 16 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
