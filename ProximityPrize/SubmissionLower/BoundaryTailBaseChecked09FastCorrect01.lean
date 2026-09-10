import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r9_part0 : ∀ i ∈ List.range 8, CorrectAt 9 (0+i) := by decide +kernel

theorem correct_r9_part1 : ∀ i ∈ List.range 8, CorrectAt 9 (8+i) := by decide +kernel

theorem correct_r9_part2 : ∀ i ∈ List.range 8, CorrectAt 9 (16+i) := by decide +kernel

theorem correct_r9_part3 : ∀ i ∈ List.range 8, CorrectAt 9 (24+i) := by decide +kernel

theorem correct_r9_part4 : ∀ i ∈ List.range 8, CorrectAt 9 (32+i) := by decide +kernel

theorem correct_r9_part5 : ∀ i ∈ List.range 8, CorrectAt 9 (40+i) := by decide +kernel

theorem correct_r9_part6 : ∀ i ∈ List.range 8, CorrectAt 9 (48+i) := by decide +kernel

theorem correct_r9_part7 : ∀ i ∈ List.range 8, CorrectAt 9 (56+i) := by decide +kernel

theorem correct_r9_part8 : ∀ i ∈ List.range 8, CorrectAt 9 (64+i) := by decide +kernel

theorem correct_r9_part9 : ∀ i ∈ List.range 8, CorrectAt 9 (72+i) := by decide +kernel

theorem correct_r9_part10 : ∀ i ∈ List.range 8, CorrectAt 9 (80+i) := by decide +kernel

theorem correct_r9_part11 : ∀ i ∈ List.range 8, CorrectAt 9 (88+i) := by decide +kernel

theorem correct_r9_part12 : ∀ i ∈ List.range 8, CorrectAt 9 (96+i) := by decide +kernel

theorem correct_r9_part13 : ∀ i ∈ List.range 8, CorrectAt 9 (104+i) := by decide +kernel

theorem correct_r9_part14 : ∀ i ∈ List.range 8, CorrectAt 9 (112+i) := by decide +kernel

theorem correct_r9_part15 : ∀ i ∈ List.range 8, CorrectAt 9 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
