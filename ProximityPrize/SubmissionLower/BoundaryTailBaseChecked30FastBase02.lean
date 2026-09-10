import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastBase01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem base_r30_part16 : ∀ i ∈ List.range 4, BaseCheckAt 30 (64+i) := by decide +kernel

theorem base_r30_part17 : ∀ i ∈ List.range 4, BaseCheckAt 30 (68+i) := by decide +kernel

theorem base_r30_part18 : ∀ i ∈ List.range 4, BaseCheckAt 30 (72+i) := by decide +kernel

theorem base_r30_part19 : ∀ i ∈ List.range 4, BaseCheckAt 30 (76+i) := by decide +kernel

theorem base_r30_part20 : ∀ i ∈ List.range 4, BaseCheckAt 30 (80+i) := by decide +kernel

theorem base_r30_part21 : ∀ i ∈ List.range 4, BaseCheckAt 30 (84+i) := by decide +kernel

theorem base_r30_part22 : ∀ i ∈ List.range 4, BaseCheckAt 30 (88+i) := by decide +kernel

theorem base_r30_part23 : ∀ i ∈ List.range 4, BaseCheckAt 30 (92+i) := by decide +kernel

theorem base_r30_part24 : ∀ i ∈ List.range 4, BaseCheckAt 30 (96+i) := by decide +kernel

theorem base_r30_part25 : ∀ i ∈ List.range 4, BaseCheckAt 30 (100+i) := by decide +kernel

theorem base_r30_part26 : ∀ i ∈ List.range 4, BaseCheckAt 30 (104+i) := by decide +kernel

theorem base_r30_part27 : ∀ i ∈ List.range 2, BaseCheckAt 30 (108+i) := by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
