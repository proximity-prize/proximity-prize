import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastZero07
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem base_r30_part0 : ∀ i ∈ List.range 4, BaseCheckAt 30 (0+i) := by decide +kernel

theorem base_r30_part1 : ∀ i ∈ List.range 4, BaseCheckAt 30 (4+i) := by decide +kernel

theorem base_r30_part2 : ∀ i ∈ List.range 4, BaseCheckAt 30 (8+i) := by decide +kernel

theorem base_r30_part3 : ∀ i ∈ List.range 4, BaseCheckAt 30 (12+i) := by decide +kernel

theorem base_r30_part4 : ∀ i ∈ List.range 4, BaseCheckAt 30 (16+i) := by decide +kernel

theorem base_r30_part5 : ∀ i ∈ List.range 4, BaseCheckAt 30 (20+i) := by decide +kernel

theorem base_r30_part6 : ∀ i ∈ List.range 4, BaseCheckAt 30 (24+i) := by decide +kernel

theorem base_r30_part7 : ∀ i ∈ List.range 4, BaseCheckAt 30 (28+i) := by decide +kernel

theorem base_r30_part8 : ∀ i ∈ List.range 4, BaseCheckAt 30 (32+i) := by decide +kernel

theorem base_r30_part9 : ∀ i ∈ List.range 4, BaseCheckAt 30 (36+i) := by decide +kernel

theorem base_r30_part10 : ∀ i ∈ List.range 4, BaseCheckAt 30 (40+i) := by decide +kernel

theorem base_r30_part11 : ∀ i ∈ List.range 4, BaseCheckAt 30 (44+i) := by decide +kernel

theorem base_r30_part12 : ∀ i ∈ List.range 4, BaseCheckAt 30 (48+i) := by decide +kernel

theorem base_r30_part13 : ∀ i ∈ List.range 4, BaseCheckAt 30 (52+i) := by decide +kernel

theorem base_r30_part14 : ∀ i ∈ List.range 4, BaseCheckAt 30 (56+i) := by decide +kernel

theorem base_r30_part15 : ∀ i ∈ List.range 4, BaseCheckAt 30 (60+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
