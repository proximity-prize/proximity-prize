import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r22_part0 : ∀ i ∈ List.range 8, CorrectAt 22 (0+i) := by decide +kernel

theorem correct_r22_part1 : ∀ i ∈ List.range 8, CorrectAt 22 (8+i) := by decide +kernel

theorem correct_r22_part2 : ∀ i ∈ List.range 8, CorrectAt 22 (16+i) := by decide +kernel

theorem correct_r22_part3 : ∀ i ∈ List.range 8, CorrectAt 22 (24+i) := by decide +kernel

theorem correct_r22_part4 : ∀ i ∈ List.range 8, CorrectAt 22 (32+i) := by decide +kernel

theorem correct_r22_part5 : ∀ i ∈ List.range 8, CorrectAt 22 (40+i) := by decide +kernel

theorem correct_r22_part6 : ∀ i ∈ List.range 8, CorrectAt 22 (48+i) := by decide +kernel

theorem correct_r22_part7 : ∀ i ∈ List.range 8, CorrectAt 22 (56+i) := by decide +kernel

theorem correct_r22_part8 : ∀ i ∈ List.range 8, CorrectAt 22 (64+i) := by decide +kernel

theorem correct_r22_part9 : ∀ i ∈ List.range 8, CorrectAt 22 (72+i) := by decide +kernel

theorem correct_r22_part10 : ∀ i ∈ List.range 8, CorrectAt 22 (80+i) := by decide +kernel

theorem correct_r22_part11 : ∀ i ∈ List.range 8, CorrectAt 22 (88+i) := by decide +kernel

theorem correct_r22_part12 : ∀ i ∈ List.range 8, CorrectAt 22 (96+i) := by decide +kernel

theorem correct_r22_part13 : ∀ i ∈ List.range 8, CorrectAt 22 (104+i) := by decide +kernel

theorem correct_r22_part14 : ∀ i ∈ List.range 6, CorrectAt 22 (112+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
