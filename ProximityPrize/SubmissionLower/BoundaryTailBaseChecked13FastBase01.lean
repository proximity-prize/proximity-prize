import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastZero09
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13FastStrict09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br13p0:∀ i ∈ List.range 4,BaseCheckAt 13 (0+i):=by decide +kernel

theorem br13p1:∀ i ∈ List.range 4,BaseCheckAt 13 (4+i):=by decide +kernel

theorem br13p2:∀ i ∈ List.range 4,BaseCheckAt 13 (8+i):=by decide +kernel

theorem br13p3:∀ i ∈ List.range 4,BaseCheckAt 13 (12+i):=by decide +kernel

theorem br13p4:∀ i ∈ List.range 4,BaseCheckAt 13 (16+i):=by decide +kernel

theorem br13p5:∀ i ∈ List.range 4,BaseCheckAt 13 (20+i):=by decide +kernel

theorem br13p6:∀ i ∈ List.range 4,BaseCheckAt 13 (24+i):=by decide +kernel

theorem br13p7:∀ i ∈ List.range 4,BaseCheckAt 13 (28+i):=by decide +kernel

theorem br13p8:∀ i ∈ List.range 4,BaseCheckAt 13 (32+i):=by decide +kernel

theorem br13p9:∀ i ∈ List.range 4,BaseCheckAt 13 (36+i):=by decide +kernel

theorem br13p10:∀ i ∈ List.range 4,BaseCheckAt 13 (40+i):=by decide +kernel

theorem br13p11:∀ i ∈ List.range 4,BaseCheckAt 13 (44+i):=by decide +kernel

theorem br13p12:∀ i ∈ List.range 4,BaseCheckAt 13 (48+i):=by decide +kernel

theorem br13p13:∀ i ∈ List.range 4,BaseCheckAt 13 (52+i):=by decide +kernel

theorem br13p14:∀ i ∈ List.range 4,BaseCheckAt 13 (56+i):=by decide +kernel

theorem br13p15:∀ i ∈ List.range 4,BaseCheckAt 13 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
