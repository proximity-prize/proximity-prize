import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem correct_r30_part0 : ∀ i ∈ List.range 8, CorrectAt 30 (0+i) := by decide +kernel

theorem correct_r30_part1 : ∀ i ∈ List.range 8, CorrectAt 30 (8+i) := by decide +kernel

theorem correct_r30_part2 : ∀ i ∈ List.range 8, CorrectAt 30 (16+i) := by decide +kernel

theorem correct_r30_part3 : ∀ i ∈ List.range 8, CorrectAt 30 (24+i) := by decide +kernel

theorem correct_r30_part4 : ∀ i ∈ List.range 8, CorrectAt 30 (32+i) := by decide +kernel

theorem correct_r30_part5 : ∀ i ∈ List.range 8, CorrectAt 30 (40+i) := by decide +kernel

theorem correct_r30_part6 : ∀ i ∈ List.range 8, CorrectAt 30 (48+i) := by decide +kernel

theorem correct_r30_part7 : ∀ i ∈ List.range 8, CorrectAt 30 (56+i) := by decide +kernel

theorem correct_r30_part8 : ∀ i ∈ List.range 8, CorrectAt 30 (64+i) := by decide +kernel

theorem correct_r30_part9 : ∀ i ∈ List.range 8, CorrectAt 30 (72+i) := by decide +kernel

theorem correct_r30_part10 : ∀ i ∈ List.range 8, CorrectAt 30 (80+i) := by decide +kernel

theorem correct_r30_part11 : ∀ i ∈ List.range 8, CorrectAt 30 (88+i) := by decide +kernel

theorem correct_r30_part12 : ∀ i ∈ List.range 8, CorrectAt 30 (96+i) := by decide +kernel

theorem correct_r30_part13 : ∀ i ∈ List.range 6, CorrectAt 30 (104+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
