import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem base_r21_part0 : ∀ i ∈ List.range 4, BaseCheckAt 21 (0+i) := by decide +kernel

theorem base_r21_part1 : ∀ i ∈ List.range 4, BaseCheckAt 21 (4+i) := by decide +kernel

theorem base_r21_part2 : ∀ i ∈ List.range 4, BaseCheckAt 21 (8+i) := by decide +kernel

theorem base_r21_part3 : ∀ i ∈ List.range 4, BaseCheckAt 21 (12+i) := by decide +kernel

theorem base_r21_part4 : ∀ i ∈ List.range 4, BaseCheckAt 21 (16+i) := by decide +kernel

theorem base_r21_part5 : ∀ i ∈ List.range 4, BaseCheckAt 21 (20+i) := by decide +kernel

theorem base_r21_part6 : ∀ i ∈ List.range 4, BaseCheckAt 21 (24+i) := by decide +kernel

theorem base_r21_part7 : ∀ i ∈ List.range 4, BaseCheckAt 21 (28+i) := by decide +kernel

theorem base_r21_part8 : ∀ i ∈ List.range 4, BaseCheckAt 21 (32+i) := by decide +kernel

theorem base_r21_part9 : ∀ i ∈ List.range 4, BaseCheckAt 21 (36+i) := by decide +kernel

theorem base_r21_part10 : ∀ i ∈ List.range 4, BaseCheckAt 21 (40+i) := by decide +kernel

theorem base_r21_part11 : ∀ i ∈ List.range 4, BaseCheckAt 21 (44+i) := by decide +kernel

theorem base_r21_part12 : ∀ i ∈ List.range 4, BaseCheckAt 21 (48+i) := by decide +kernel

theorem base_r21_part13 : ∀ i ∈ List.range 4, BaseCheckAt 21 (52+i) := by decide +kernel

theorem base_r21_part14 : ∀ i ∈ List.range 4, BaseCheckAt 21 (56+i) := by decide +kernel

theorem base_r21_part15 : ∀ i ∈ List.range 4, BaseCheckAt 21 (60+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
