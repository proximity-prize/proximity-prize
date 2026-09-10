import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r17_part0 : ∀ i ∈ List.range 8, CorrectAt 17 (0+i) := by decide +kernel

theorem correct_r17_part1 : ∀ i ∈ List.range 8, CorrectAt 17 (8+i) := by decide +kernel

theorem correct_r17_part2 : ∀ i ∈ List.range 8, CorrectAt 17 (16+i) := by decide +kernel

theorem correct_r17_part3 : ∀ i ∈ List.range 8, CorrectAt 17 (24+i) := by decide +kernel

theorem correct_r17_part4 : ∀ i ∈ List.range 8, CorrectAt 17 (32+i) := by decide +kernel

theorem correct_r17_part5 : ∀ i ∈ List.range 8, CorrectAt 17 (40+i) := by decide +kernel

theorem correct_r17_part6 : ∀ i ∈ List.range 8, CorrectAt 17 (48+i) := by decide +kernel

theorem correct_r17_part7 : ∀ i ∈ List.range 8, CorrectAt 17 (56+i) := by decide +kernel

theorem correct_r17_part8 : ∀ i ∈ List.range 8, CorrectAt 17 (64+i) := by decide +kernel

theorem correct_r17_part9 : ∀ i ∈ List.range 8, CorrectAt 17 (72+i) := by decide +kernel

theorem correct_r17_part10 : ∀ i ∈ List.range 8, CorrectAt 17 (80+i) := by decide +kernel

theorem correct_r17_part11 : ∀ i ∈ List.range 8, CorrectAt 17 (88+i) := by decide +kernel

theorem correct_r17_part12 : ∀ i ∈ List.range 8, CorrectAt 17 (96+i) := by decide +kernel

theorem correct_r17_part13 : ∀ i ∈ List.range 8, CorrectAt 17 (104+i) := by decide +kernel

theorem correct_r17_part14 : ∀ i ∈ List.range 8, CorrectAt 17 (112+i) := by decide +kernel

theorem correct_r17_part15 : ∀ i ∈ List.range 3, CorrectAt 17 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
