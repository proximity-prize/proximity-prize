import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked05

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r6_part0 : ∀ i ∈ List.range 8, CorrectAt 6 (0+i) := by decide +kernel

theorem correct_r6_part1 : ∀ i ∈ List.range 8, CorrectAt 6 (8+i) := by decide +kernel

theorem correct_r6_part2 : ∀ i ∈ List.range 8, CorrectAt 6 (16+i) := by decide +kernel

theorem correct_r6_part3 : ∀ i ∈ List.range 8, CorrectAt 6 (24+i) := by decide +kernel

theorem correct_r6_part4 : ∀ i ∈ List.range 8, CorrectAt 6 (32+i) := by decide +kernel

theorem correct_r6_part5 : ∀ i ∈ List.range 8, CorrectAt 6 (40+i) := by decide +kernel

theorem correct_r6_part6 : ∀ i ∈ List.range 8, CorrectAt 6 (48+i) := by decide +kernel

theorem correct_r6_part7 : ∀ i ∈ List.range 8, CorrectAt 6 (56+i) := by decide +kernel

theorem correct_r6_part8 : ∀ i ∈ List.range 8, CorrectAt 6 (64+i) := by decide +kernel

theorem correct_r6_part9 : ∀ i ∈ List.range 8, CorrectAt 6 (72+i) := by decide +kernel

theorem correct_r6_part10 : ∀ i ∈ List.range 8, CorrectAt 6 (80+i) := by decide +kernel

theorem correct_r6_part11 : ∀ i ∈ List.range 8, CorrectAt 6 (88+i) := by decide +kernel

theorem correct_r6_part12 : ∀ i ∈ List.range 8, CorrectAt 6 (96+i) := by decide +kernel

theorem correct_r6_part13 : ∀ i ∈ List.range 8, CorrectAt 6 (104+i) := by decide +kernel

theorem correct_r6_part14 : ∀ i ∈ List.range 8, CorrectAt 6 (112+i) := by decide +kernel

theorem correct_r6_part15 : ∀ i ∈ List.range 8, CorrectAt 6 (120+i) := by decide +kernel

theorem correct_r6_part16 : ∀ i ∈ List.range 6, CorrectAt 6 (128+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
