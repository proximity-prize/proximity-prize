import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r21_part0 : ∀ i ∈ List.range 8, CorrectAt 21 (0+i) := by decide +kernel

theorem correct_r21_part1 : ∀ i ∈ List.range 8, CorrectAt 21 (8+i) := by decide +kernel

theorem correct_r21_part2 : ∀ i ∈ List.range 8, CorrectAt 21 (16+i) := by decide +kernel

theorem correct_r21_part3 : ∀ i ∈ List.range 8, CorrectAt 21 (24+i) := by decide +kernel

theorem correct_r21_part4 : ∀ i ∈ List.range 8, CorrectAt 21 (32+i) := by decide +kernel

theorem correct_r21_part5 : ∀ i ∈ List.range 8, CorrectAt 21 (40+i) := by decide +kernel

theorem correct_r21_part6 : ∀ i ∈ List.range 8, CorrectAt 21 (48+i) := by decide +kernel

theorem correct_r21_part7 : ∀ i ∈ List.range 8, CorrectAt 21 (56+i) := by decide +kernel

theorem correct_r21_part8 : ∀ i ∈ List.range 8, CorrectAt 21 (64+i) := by decide +kernel

theorem correct_r21_part9 : ∀ i ∈ List.range 8, CorrectAt 21 (72+i) := by decide +kernel

theorem correct_r21_part10 : ∀ i ∈ List.range 8, CorrectAt 21 (80+i) := by decide +kernel

theorem correct_r21_part11 : ∀ i ∈ List.range 8, CorrectAt 21 (88+i) := by decide +kernel

theorem correct_r21_part12 : ∀ i ∈ List.range 8, CorrectAt 21 (96+i) := by decide +kernel

theorem correct_r21_part13 : ∀ i ∈ List.range 8, CorrectAt 21 (104+i) := by decide +kernel

theorem correct_r21_part14 : ∀ i ∈ List.range 7, CorrectAt 21 (112+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
