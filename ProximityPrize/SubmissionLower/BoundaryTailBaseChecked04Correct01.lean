import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r4_part0 : ∀ i ∈ List.range 8, CorrectAt 4 (0+i) := by decide +kernel

theorem correct_r4_part1 : ∀ i ∈ List.range 8, CorrectAt 4 (8+i) := by decide +kernel

theorem correct_r4_part2 : ∀ i ∈ List.range 8, CorrectAt 4 (16+i) := by decide +kernel

theorem correct_r4_part3 : ∀ i ∈ List.range 8, CorrectAt 4 (24+i) := by decide +kernel

theorem correct_r4_part4 : ∀ i ∈ List.range 8, CorrectAt 4 (32+i) := by decide +kernel

theorem correct_r4_part5 : ∀ i ∈ List.range 8, CorrectAt 4 (40+i) := by decide +kernel

theorem correct_r4_part6 : ∀ i ∈ List.range 8, CorrectAt 4 (48+i) := by decide +kernel

theorem correct_r4_part7 : ∀ i ∈ List.range 8, CorrectAt 4 (56+i) := by decide +kernel

theorem correct_r4_part8 : ∀ i ∈ List.range 8, CorrectAt 4 (64+i) := by decide +kernel

theorem correct_r4_part9 : ∀ i ∈ List.range 8, CorrectAt 4 (72+i) := by decide +kernel

theorem correct_r4_part10 : ∀ i ∈ List.range 8, CorrectAt 4 (80+i) := by decide +kernel

theorem correct_r4_part11 : ∀ i ∈ List.range 8, CorrectAt 4 (88+i) := by decide +kernel

theorem correct_r4_part12 : ∀ i ∈ List.range 8, CorrectAt 4 (96+i) := by decide +kernel

theorem correct_r4_part13 : ∀ i ∈ List.range 8, CorrectAt 4 (104+i) := by decide +kernel

theorem correct_r4_part14 : ∀ i ∈ List.range 8, CorrectAt 4 (112+i) := by decide +kernel

theorem correct_r4_part15 : ∀ i ∈ List.range 8, CorrectAt 4 (120+i) := by decide +kernel

theorem correct_r4_part16 : ∀ i ∈ List.range 8, CorrectAt 4 (128+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
