import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r24_part0 : ∀ i ∈ List.range 8, CorrectAt 24 (0+i) := by decide +kernel

theorem correct_r24_part1 : ∀ i ∈ List.range 8, CorrectAt 24 (8+i) := by decide +kernel

theorem correct_r24_part2 : ∀ i ∈ List.range 8, CorrectAt 24 (16+i) := by decide +kernel

theorem correct_r24_part3 : ∀ i ∈ List.range 8, CorrectAt 24 (24+i) := by decide +kernel

theorem correct_r24_part4 : ∀ i ∈ List.range 8, CorrectAt 24 (32+i) := by decide +kernel

theorem correct_r24_part5 : ∀ i ∈ List.range 8, CorrectAt 24 (40+i) := by decide +kernel

theorem correct_r24_part6 : ∀ i ∈ List.range 8, CorrectAt 24 (48+i) := by decide +kernel

theorem correct_r24_part7 : ∀ i ∈ List.range 8, CorrectAt 24 (56+i) := by decide +kernel

theorem correct_r24_part8 : ∀ i ∈ List.range 8, CorrectAt 24 (64+i) := by decide +kernel

theorem correct_r24_part9 : ∀ i ∈ List.range 8, CorrectAt 24 (72+i) := by decide +kernel

theorem correct_r24_part10 : ∀ i ∈ List.range 8, CorrectAt 24 (80+i) := by decide +kernel

theorem correct_r24_part11 : ∀ i ∈ List.range 8, CorrectAt 24 (88+i) := by decide +kernel

theorem correct_r24_part12 : ∀ i ∈ List.range 8, CorrectAt 24 (96+i) := by decide +kernel

theorem correct_r24_part13 : ∀ i ∈ List.range 8, CorrectAt 24 (104+i) := by decide +kernel

theorem correct_r24_part14 : ∀ i ∈ List.range 4, CorrectAt 24 (112+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
