import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem base_r25_part0 : ∀ i ∈ List.range 4, BaseCheckAt 25 (0+i) := by decide +kernel

theorem base_r25_part1 : ∀ i ∈ List.range 4, BaseCheckAt 25 (4+i) := by decide +kernel

theorem base_r25_part2 : ∀ i ∈ List.range 4, BaseCheckAt 25 (8+i) := by decide +kernel

theorem base_r25_part3 : ∀ i ∈ List.range 4, BaseCheckAt 25 (12+i) := by decide +kernel

theorem base_r25_part4 : ∀ i ∈ List.range 4, BaseCheckAt 25 (16+i) := by decide +kernel

theorem base_r25_part5 : ∀ i ∈ List.range 4, BaseCheckAt 25 (20+i) := by decide +kernel

theorem base_r25_part6 : ∀ i ∈ List.range 4, BaseCheckAt 25 (24+i) := by decide +kernel

theorem base_r25_part7 : ∀ i ∈ List.range 4, BaseCheckAt 25 (28+i) := by decide +kernel

theorem base_r25_part8 : ∀ i ∈ List.range 4, BaseCheckAt 25 (32+i) := by decide +kernel

theorem base_r25_part9 : ∀ i ∈ List.range 4, BaseCheckAt 25 (36+i) := by decide +kernel

theorem base_r25_part10 : ∀ i ∈ List.range 4, BaseCheckAt 25 (40+i) := by decide +kernel

theorem base_r25_part11 : ∀ i ∈ List.range 4, BaseCheckAt 25 (44+i) := by decide +kernel

theorem base_r25_part12 : ∀ i ∈ List.range 4, BaseCheckAt 25 (48+i) := by decide +kernel

theorem base_r25_part13 : ∀ i ∈ List.range 4, BaseCheckAt 25 (52+i) := by decide +kernel

theorem base_r25_part14 : ∀ i ∈ List.range 4, BaseCheckAt 25 (56+i) := by decide +kernel

theorem base_r25_part15 : ∀ i ∈ List.range 4, BaseCheckAt 25 (60+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
