import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem base_r18_part0 : ∀ i ∈ List.range 4, BaseCheckAt 18 (0+i) := by decide +kernel

theorem base_r18_part1 : ∀ i ∈ List.range 4, BaseCheckAt 18 (4+i) := by decide +kernel

theorem base_r18_part2 : ∀ i ∈ List.range 4, BaseCheckAt 18 (8+i) := by decide +kernel

theorem base_r18_part3 : ∀ i ∈ List.range 4, BaseCheckAt 18 (12+i) := by decide +kernel

theorem base_r18_part4 : ∀ i ∈ List.range 4, BaseCheckAt 18 (16+i) := by decide +kernel

theorem base_r18_part5 : ∀ i ∈ List.range 4, BaseCheckAt 18 (20+i) := by decide +kernel

theorem base_r18_part6 : ∀ i ∈ List.range 4, BaseCheckAt 18 (24+i) := by decide +kernel

theorem base_r18_part7 : ∀ i ∈ List.range 4, BaseCheckAt 18 (28+i) := by decide +kernel

theorem base_r18_part8 : ∀ i ∈ List.range 4, BaseCheckAt 18 (32+i) := by decide +kernel

theorem base_r18_part9 : ∀ i ∈ List.range 4, BaseCheckAt 18 (36+i) := by decide +kernel

theorem base_r18_part10 : ∀ i ∈ List.range 4, BaseCheckAt 18 (40+i) := by decide +kernel

theorem base_r18_part11 : ∀ i ∈ List.range 4, BaseCheckAt 18 (44+i) := by decide +kernel

theorem base_r18_part12 : ∀ i ∈ List.range 4, BaseCheckAt 18 (48+i) := by decide +kernel

theorem base_r18_part13 : ∀ i ∈ List.range 4, BaseCheckAt 18 (52+i) := by decide +kernel

theorem base_r18_part14 : ∀ i ∈ List.range 4, BaseCheckAt 18 (56+i) := by decide +kernel

theorem base_r18_part15 : ∀ i ∈ List.range 4, BaseCheckAt 18 (60+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
