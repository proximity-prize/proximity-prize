import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br25p0:∀ i ∈ List.range 4,BaseCheckAt 25 (0+i):=by decide +kernel

theorem br25p1:∀ i ∈ List.range 4,BaseCheckAt 25 (4+i):=by decide +kernel

theorem br25p2:∀ i ∈ List.range 4,BaseCheckAt 25 (8+i):=by decide +kernel

theorem br25p3:∀ i ∈ List.range 4,BaseCheckAt 25 (12+i):=by decide +kernel

theorem br25p4:∀ i ∈ List.range 4,BaseCheckAt 25 (16+i):=by decide +kernel

theorem br25p5:∀ i ∈ List.range 4,BaseCheckAt 25 (20+i):=by decide +kernel

theorem br25p6:∀ i ∈ List.range 4,BaseCheckAt 25 (24+i):=by decide +kernel

theorem br25p7:∀ i ∈ List.range 4,BaseCheckAt 25 (28+i):=by decide +kernel

theorem br25p8:∀ i ∈ List.range 4,BaseCheckAt 25 (32+i):=by decide +kernel

theorem br25p9:∀ i ∈ List.range 4,BaseCheckAt 25 (36+i):=by decide +kernel

theorem br25p10:∀ i ∈ List.range 4,BaseCheckAt 25 (40+i):=by decide +kernel

theorem br25p11:∀ i ∈ List.range 4,BaseCheckAt 25 (44+i):=by decide +kernel

theorem br25p12:∀ i ∈ List.range 4,BaseCheckAt 25 (48+i):=by decide +kernel

theorem br25p13:∀ i ∈ List.range 4,BaseCheckAt 25 (52+i):=by decide +kernel

theorem br25p14:∀ i ∈ List.range 4,BaseCheckAt 25 (56+i):=by decide +kernel

theorem br25p15:∀ i ∈ List.range 4,BaseCheckAt 25 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
