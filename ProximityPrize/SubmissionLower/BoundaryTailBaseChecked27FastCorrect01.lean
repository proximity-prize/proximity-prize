import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r27_part0 : ∀ i ∈ List.range 8, CorrectAt 27 (0+i) := by decide +kernel

theorem correct_r27_part1 : ∀ i ∈ List.range 8, CorrectAt 27 (8+i) := by decide +kernel

theorem correct_r27_part2 : ∀ i ∈ List.range 8, CorrectAt 27 (16+i) := by decide +kernel

theorem correct_r27_part3 : ∀ i ∈ List.range 8, CorrectAt 27 (24+i) := by decide +kernel

theorem correct_r27_part4 : ∀ i ∈ List.range 8, CorrectAt 27 (32+i) := by decide +kernel

theorem correct_r27_part5 : ∀ i ∈ List.range 8, CorrectAt 27 (40+i) := by decide +kernel

theorem correct_r27_part6 : ∀ i ∈ List.range 8, CorrectAt 27 (48+i) := by decide +kernel

theorem correct_r27_part7 : ∀ i ∈ List.range 8, CorrectAt 27 (56+i) := by decide +kernel

theorem correct_r27_part8 : ∀ i ∈ List.range 8, CorrectAt 27 (64+i) := by decide +kernel

theorem correct_r27_part9 : ∀ i ∈ List.range 8, CorrectAt 27 (72+i) := by decide +kernel

theorem correct_r27_part10 : ∀ i ∈ List.range 8, CorrectAt 27 (80+i) := by decide +kernel

theorem correct_r27_part11 : ∀ i ∈ List.range 8, CorrectAt 27 (88+i) := by decide +kernel

theorem correct_r27_part12 : ∀ i ∈ List.range 8, CorrectAt 27 (96+i) := by decide +kernel

theorem correct_r27_part13 : ∀ i ∈ List.range 8, CorrectAt 27 (104+i) := by decide +kernel

theorem correct_r27_part14 : ∀ i ∈ List.range 1, CorrectAt 27 (112+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
