import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r2_part0 : ∀ i ∈ List.range 8, CorrectAt 2 (0+i) := by decide +kernel

theorem correct_r2_part1 : ∀ i ∈ List.range 8, CorrectAt 2 (8+i) := by decide +kernel

theorem correct_r2_part2 : ∀ i ∈ List.range 8, CorrectAt 2 (16+i) := by decide +kernel

theorem correct_r2_part3 : ∀ i ∈ List.range 8, CorrectAt 2 (24+i) := by decide +kernel

theorem correct_r2_part4 : ∀ i ∈ List.range 8, CorrectAt 2 (32+i) := by decide +kernel

theorem correct_r2_part5 : ∀ i ∈ List.range 8, CorrectAt 2 (40+i) := by decide +kernel

theorem correct_r2_part6 : ∀ i ∈ List.range 8, CorrectAt 2 (48+i) := by decide +kernel

theorem correct_r2_part7 : ∀ i ∈ List.range 8, CorrectAt 2 (56+i) := by decide +kernel

theorem correct_r2_part8 : ∀ i ∈ List.range 8, CorrectAt 2 (64+i) := by decide +kernel

theorem correct_r2_part9 : ∀ i ∈ List.range 8, CorrectAt 2 (72+i) := by decide +kernel

theorem correct_r2_part10 : ∀ i ∈ List.range 8, CorrectAt 2 (80+i) := by decide +kernel

theorem correct_r2_part11 : ∀ i ∈ List.range 8, CorrectAt 2 (88+i) := by decide +kernel

theorem correct_r2_part12 : ∀ i ∈ List.range 8, CorrectAt 2 (96+i) := by decide +kernel

theorem correct_r2_part13 : ∀ i ∈ List.range 8, CorrectAt 2 (104+i) := by decide +kernel

theorem correct_r2_part14 : ∀ i ∈ List.range 8, CorrectAt 2 (112+i) := by decide +kernel

theorem correct_r2_part15 : ∀ i ∈ List.range 8, CorrectAt 2 (120+i) := by decide +kernel

theorem correct_r2_part16 : ∀ i ∈ List.range 8, CorrectAt 2 (128+i) := by decide +kernel

theorem correct_r2_part17 : ∀ i ∈ List.range 2, CorrectAt 2 (136+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
