import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br18p0:∀ i ∈ List.range 4,BaseCheckAt 18 (0+i):=by decide +kernel

theorem br18p1:∀ i ∈ List.range 4,BaseCheckAt 18 (4+i):=by decide +kernel

theorem br18p2:∀ i ∈ List.range 4,BaseCheckAt 18 (8+i):=by decide +kernel

theorem br18p3:∀ i ∈ List.range 4,BaseCheckAt 18 (12+i):=by decide +kernel

theorem br18p4:∀ i ∈ List.range 4,BaseCheckAt 18 (16+i):=by decide +kernel

theorem br18p5:∀ i ∈ List.range 4,BaseCheckAt 18 (20+i):=by decide +kernel

theorem br18p6:∀ i ∈ List.range 4,BaseCheckAt 18 (24+i):=by decide +kernel

theorem br18p7:∀ i ∈ List.range 4,BaseCheckAt 18 (28+i):=by decide +kernel

theorem br18p8:∀ i ∈ List.range 4,BaseCheckAt 18 (32+i):=by decide +kernel

theorem br18p9:∀ i ∈ List.range 4,BaseCheckAt 18 (36+i):=by decide +kernel

theorem br18p10:∀ i ∈ List.range 4,BaseCheckAt 18 (40+i):=by decide +kernel

theorem br18p11:∀ i ∈ List.range 4,BaseCheckAt 18 (44+i):=by decide +kernel

theorem br18p12:∀ i ∈ List.range 4,BaseCheckAt 18 (48+i):=by decide +kernel

theorem br18p13:∀ i ∈ List.range 4,BaseCheckAt 18 (52+i):=by decide +kernel

theorem br18p14:∀ i ∈ List.range 4,BaseCheckAt 18 (56+i):=by decide +kernel

theorem br18p15:∀ i ∈ List.range 4,BaseCheckAt 18 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
