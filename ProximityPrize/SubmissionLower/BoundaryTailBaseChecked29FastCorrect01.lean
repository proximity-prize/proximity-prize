import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked28

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r29_part0 : ∀ i ∈ List.range 8, CorrectAt 29 (0+i) := by decide +kernel

theorem correct_r29_part1 : ∀ i ∈ List.range 8, CorrectAt 29 (8+i) := by decide +kernel

theorem correct_r29_part2 : ∀ i ∈ List.range 8, CorrectAt 29 (16+i) := by decide +kernel

theorem correct_r29_part3 : ∀ i ∈ List.range 8, CorrectAt 29 (24+i) := by decide +kernel

theorem correct_r29_part4 : ∀ i ∈ List.range 8, CorrectAt 29 (32+i) := by decide +kernel

theorem correct_r29_part5 : ∀ i ∈ List.range 8, CorrectAt 29 (40+i) := by decide +kernel

theorem correct_r29_part6 : ∀ i ∈ List.range 8, CorrectAt 29 (48+i) := by decide +kernel

theorem correct_r29_part7 : ∀ i ∈ List.range 8, CorrectAt 29 (56+i) := by decide +kernel

theorem correct_r29_part8 : ∀ i ∈ List.range 8, CorrectAt 29 (64+i) := by decide +kernel

theorem correct_r29_part9 : ∀ i ∈ List.range 8, CorrectAt 29 (72+i) := by decide +kernel

theorem correct_r29_part10 : ∀ i ∈ List.range 8, CorrectAt 29 (80+i) := by decide +kernel

theorem correct_r29_part11 : ∀ i ∈ List.range 8, CorrectAt 29 (88+i) := by decide +kernel

theorem correct_r29_part12 : ∀ i ∈ List.range 8, CorrectAt 29 (96+i) := by decide +kernel

theorem correct_r29_part13 : ∀ i ∈ List.range 7, CorrectAt 29 (104+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
