import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r11_part0 : ∀ i ∈ List.range 8, CorrectAt 11 (0+i) := by decide +kernel

theorem correct_r11_part1 : ∀ i ∈ List.range 8, CorrectAt 11 (8+i) := by decide +kernel

theorem correct_r11_part2 : ∀ i ∈ List.range 8, CorrectAt 11 (16+i) := by decide +kernel

theorem correct_r11_part3 : ∀ i ∈ List.range 8, CorrectAt 11 (24+i) := by decide +kernel

theorem correct_r11_part4 : ∀ i ∈ List.range 8, CorrectAt 11 (32+i) := by decide +kernel

theorem correct_r11_part5 : ∀ i ∈ List.range 8, CorrectAt 11 (40+i) := by decide +kernel

theorem correct_r11_part6 : ∀ i ∈ List.range 8, CorrectAt 11 (48+i) := by decide +kernel

theorem correct_r11_part7 : ∀ i ∈ List.range 8, CorrectAt 11 (56+i) := by decide +kernel

theorem correct_r11_part8 : ∀ i ∈ List.range 8, CorrectAt 11 (64+i) := by decide +kernel

theorem correct_r11_part9 : ∀ i ∈ List.range 8, CorrectAt 11 (72+i) := by decide +kernel

theorem correct_r11_part10 : ∀ i ∈ List.range 8, CorrectAt 11 (80+i) := by decide +kernel

theorem correct_r11_part11 : ∀ i ∈ List.range 8, CorrectAt 11 (88+i) := by decide +kernel

theorem correct_r11_part12 : ∀ i ∈ List.range 8, CorrectAt 11 (96+i) := by decide +kernel

theorem correct_r11_part13 : ∀ i ∈ List.range 8, CorrectAt 11 (104+i) := by decide +kernel

theorem correct_r11_part14 : ∀ i ∈ List.range 8, CorrectAt 11 (112+i) := by decide +kernel

theorem correct_r11_part15 : ∀ i ∈ List.range 8, CorrectAt 11 (120+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
