import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r28_part0 : ∀ i ∈ List.range 8, CorrectAt 28 (0+i) := by decide +kernel

theorem correct_r28_part1 : ∀ i ∈ List.range 8, CorrectAt 28 (8+i) := by decide +kernel

theorem correct_r28_part2 : ∀ i ∈ List.range 8, CorrectAt 28 (16+i) := by decide +kernel

theorem correct_r28_part3 : ∀ i ∈ List.range 8, CorrectAt 28 (24+i) := by decide +kernel

theorem correct_r28_part4 : ∀ i ∈ List.range 8, CorrectAt 28 (32+i) := by decide +kernel

theorem correct_r28_part5 : ∀ i ∈ List.range 8, CorrectAt 28 (40+i) := by decide +kernel

theorem correct_r28_part6 : ∀ i ∈ List.range 8, CorrectAt 28 (48+i) := by decide +kernel

theorem correct_r28_part7 : ∀ i ∈ List.range 8, CorrectAt 28 (56+i) := by decide +kernel

theorem correct_r28_part8 : ∀ i ∈ List.range 8, CorrectAt 28 (64+i) := by decide +kernel

theorem correct_r28_part9 : ∀ i ∈ List.range 8, CorrectAt 28 (72+i) := by decide +kernel

theorem correct_r28_part10 : ∀ i ∈ List.range 8, CorrectAt 28 (80+i) := by decide +kernel

theorem correct_r28_part11 : ∀ i ∈ List.range 8, CorrectAt 28 (88+i) := by decide +kernel

theorem correct_r28_part12 : ∀ i ∈ List.range 8, CorrectAt 28 (96+i) := by decide +kernel

theorem correct_r28_part13 : ∀ i ∈ List.range 8, CorrectAt 28 (104+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
