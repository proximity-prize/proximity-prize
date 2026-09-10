import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r10_part0 : ∀ i ∈ List.range 8, CorrectAt 10 (0+i) := by decide +kernel

theorem correct_r10_part1 : ∀ i ∈ List.range 8, CorrectAt 10 (8+i) := by decide +kernel

theorem correct_r10_part2 : ∀ i ∈ List.range 8, CorrectAt 10 (16+i) := by decide +kernel

theorem correct_r10_part3 : ∀ i ∈ List.range 8, CorrectAt 10 (24+i) := by decide +kernel

theorem correct_r10_part4 : ∀ i ∈ List.range 8, CorrectAt 10 (32+i) := by decide +kernel

theorem correct_r10_part5 : ∀ i ∈ List.range 8, CorrectAt 10 (40+i) := by decide +kernel

theorem correct_r10_part6 : ∀ i ∈ List.range 8, CorrectAt 10 (48+i) := by decide +kernel

theorem correct_r10_part7 : ∀ i ∈ List.range 8, CorrectAt 10 (56+i) := by decide +kernel

theorem correct_r10_part8 : ∀ i ∈ List.range 8, CorrectAt 10 (64+i) := by decide +kernel

theorem correct_r10_part9 : ∀ i ∈ List.range 8, CorrectAt 10 (72+i) := by decide +kernel

theorem correct_r10_part10 : ∀ i ∈ List.range 8, CorrectAt 10 (80+i) := by decide +kernel

theorem correct_r10_part11 : ∀ i ∈ List.range 8, CorrectAt 10 (88+i) := by decide +kernel

theorem correct_r10_part12 : ∀ i ∈ List.range 8, CorrectAt 10 (96+i) := by decide +kernel

theorem correct_r10_part13 : ∀ i ∈ List.range 8, CorrectAt 10 (104+i) := by decide +kernel

theorem correct_r10_part14 : ∀ i ∈ List.range 8, CorrectAt 10 (112+i) := by decide +kernel

theorem correct_r10_part15 : ∀ i ∈ List.range 8, CorrectAt 10 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
