import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r26_part0 : ∀ i ∈ List.range 8, CorrectAt 26 (0+i) := by decide +kernel

theorem correct_r26_part1 : ∀ i ∈ List.range 8, CorrectAt 26 (8+i) := by decide +kernel

theorem correct_r26_part2 : ∀ i ∈ List.range 8, CorrectAt 26 (16+i) := by decide +kernel

theorem correct_r26_part3 : ∀ i ∈ List.range 8, CorrectAt 26 (24+i) := by decide +kernel

theorem correct_r26_part4 : ∀ i ∈ List.range 8, CorrectAt 26 (32+i) := by decide +kernel

theorem correct_r26_part5 : ∀ i ∈ List.range 8, CorrectAt 26 (40+i) := by decide +kernel

theorem correct_r26_part6 : ∀ i ∈ List.range 8, CorrectAt 26 (48+i) := by decide +kernel

theorem correct_r26_part7 : ∀ i ∈ List.range 8, CorrectAt 26 (56+i) := by decide +kernel

theorem correct_r26_part8 : ∀ i ∈ List.range 8, CorrectAt 26 (64+i) := by decide +kernel

theorem correct_r26_part9 : ∀ i ∈ List.range 8, CorrectAt 26 (72+i) := by decide +kernel

theorem correct_r26_part10 : ∀ i ∈ List.range 8, CorrectAt 26 (80+i) := by decide +kernel

theorem correct_r26_part11 : ∀ i ∈ List.range 8, CorrectAt 26 (88+i) := by decide +kernel

theorem correct_r26_part12 : ∀ i ∈ List.range 8, CorrectAt 26 (96+i) := by decide +kernel

theorem correct_r26_part13 : ∀ i ∈ List.range 8, CorrectAt 26 (104+i) := by decide +kernel

theorem correct_r26_part14 : ∀ i ∈ List.range 2, CorrectAt 26 (112+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
