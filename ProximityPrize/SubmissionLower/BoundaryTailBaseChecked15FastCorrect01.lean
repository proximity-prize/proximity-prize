import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r15_part0 : ∀ i ∈ List.range 8, CorrectAt 15 (0+i) := by decide +kernel

theorem correct_r15_part1 : ∀ i ∈ List.range 8, CorrectAt 15 (8+i) := by decide +kernel

theorem correct_r15_part2 : ∀ i ∈ List.range 8, CorrectAt 15 (16+i) := by decide +kernel

theorem correct_r15_part3 : ∀ i ∈ List.range 8, CorrectAt 15 (24+i) := by decide +kernel

theorem correct_r15_part4 : ∀ i ∈ List.range 8, CorrectAt 15 (32+i) := by decide +kernel

theorem correct_r15_part5 : ∀ i ∈ List.range 8, CorrectAt 15 (40+i) := by decide +kernel

theorem correct_r15_part6 : ∀ i ∈ List.range 8, CorrectAt 15 (48+i) := by decide +kernel

theorem correct_r15_part7 : ∀ i ∈ List.range 8, CorrectAt 15 (56+i) := by decide +kernel

theorem correct_r15_part8 : ∀ i ∈ List.range 8, CorrectAt 15 (64+i) := by decide +kernel

theorem correct_r15_part9 : ∀ i ∈ List.range 8, CorrectAt 15 (72+i) := by decide +kernel

theorem correct_r15_part10 : ∀ i ∈ List.range 8, CorrectAt 15 (80+i) := by decide +kernel

theorem correct_r15_part11 : ∀ i ∈ List.range 8, CorrectAt 15 (88+i) := by decide +kernel

theorem correct_r15_part12 : ∀ i ∈ List.range 8, CorrectAt 15 (96+i) := by decide +kernel

theorem correct_r15_part13 : ∀ i ∈ List.range 8, CorrectAt 15 (104+i) := by decide +kernel

theorem correct_r15_part14 : ∀ i ∈ List.range 8, CorrectAt 15 (112+i) := by decide +kernel

theorem correct_r15_part15 : ∀ i ∈ List.range 5, CorrectAt 15 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
