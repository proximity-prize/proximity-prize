import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r20_part0 : ∀ i ∈ List.range 8, CorrectAt 20 (0+i) := by decide +kernel

theorem correct_r20_part1 : ∀ i ∈ List.range 8, CorrectAt 20 (8+i) := by decide +kernel

theorem correct_r20_part2 : ∀ i ∈ List.range 8, CorrectAt 20 (16+i) := by decide +kernel

theorem correct_r20_part3 : ∀ i ∈ List.range 8, CorrectAt 20 (24+i) := by decide +kernel

theorem correct_r20_part4 : ∀ i ∈ List.range 8, CorrectAt 20 (32+i) := by decide +kernel

theorem correct_r20_part5 : ∀ i ∈ List.range 8, CorrectAt 20 (40+i) := by decide +kernel

theorem correct_r20_part6 : ∀ i ∈ List.range 8, CorrectAt 20 (48+i) := by decide +kernel

theorem correct_r20_part7 : ∀ i ∈ List.range 8, CorrectAt 20 (56+i) := by decide +kernel

theorem correct_r20_part8 : ∀ i ∈ List.range 8, CorrectAt 20 (64+i) := by decide +kernel

theorem correct_r20_part9 : ∀ i ∈ List.range 8, CorrectAt 20 (72+i) := by decide +kernel

theorem correct_r20_part10 : ∀ i ∈ List.range 8, CorrectAt 20 (80+i) := by decide +kernel

theorem correct_r20_part11 : ∀ i ∈ List.range 8, CorrectAt 20 (88+i) := by decide +kernel

theorem correct_r20_part12 : ∀ i ∈ List.range 8, CorrectAt 20 (96+i) := by decide +kernel

theorem correct_r20_part13 : ∀ i ∈ List.range 8, CorrectAt 20 (104+i) := by decide +kernel

theorem correct_r20_part14 : ∀ i ∈ List.range 8, CorrectAt 20 (112+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
