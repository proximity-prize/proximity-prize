import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r13_part0 : ∀ i ∈ List.range 8, CorrectAt 13 (0+i) := by decide +kernel

theorem correct_r13_part1 : ∀ i ∈ List.range 8, CorrectAt 13 (8+i) := by decide +kernel

theorem correct_r13_part2 : ∀ i ∈ List.range 8, CorrectAt 13 (16+i) := by decide +kernel

theorem correct_r13_part3 : ∀ i ∈ List.range 8, CorrectAt 13 (24+i) := by decide +kernel

theorem correct_r13_part4 : ∀ i ∈ List.range 8, CorrectAt 13 (32+i) := by decide +kernel

theorem correct_r13_part5 : ∀ i ∈ List.range 8, CorrectAt 13 (40+i) := by decide +kernel

theorem correct_r13_part6 : ∀ i ∈ List.range 8, CorrectAt 13 (48+i) := by decide +kernel

theorem correct_r13_part7 : ∀ i ∈ List.range 8, CorrectAt 13 (56+i) := by decide +kernel

theorem correct_r13_part8 : ∀ i ∈ List.range 8, CorrectAt 13 (64+i) := by decide +kernel

theorem correct_r13_part9 : ∀ i ∈ List.range 8, CorrectAt 13 (72+i) := by decide +kernel

theorem correct_r13_part10 : ∀ i ∈ List.range 8, CorrectAt 13 (80+i) := by decide +kernel

theorem correct_r13_part11 : ∀ i ∈ List.range 8, CorrectAt 13 (88+i) := by decide +kernel

theorem correct_r13_part12 : ∀ i ∈ List.range 8, CorrectAt 13 (96+i) := by decide +kernel

theorem correct_r13_part13 : ∀ i ∈ List.range 8, CorrectAt 13 (104+i) := by decide +kernel

theorem correct_r13_part14 : ∀ i ∈ List.range 8, CorrectAt 13 (112+i) := by decide +kernel

theorem correct_r13_part15 : ∀ i ∈ List.range 7, CorrectAt 13 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
