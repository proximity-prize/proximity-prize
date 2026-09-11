import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br20p0:∀ i ∈ List.range 4,BaseCheckAt 20 (0+i):=by decide +kernel

theorem br20p1:∀ i ∈ List.range 4,BaseCheckAt 20 (4+i):=by decide +kernel

theorem br20p2:∀ i ∈ List.range 4,BaseCheckAt 20 (8+i):=by decide +kernel

theorem br20p3:∀ i ∈ List.range 4,BaseCheckAt 20 (12+i):=by decide +kernel

theorem br20p4:∀ i ∈ List.range 4,BaseCheckAt 20 (16+i):=by decide +kernel

theorem br20p5:∀ i ∈ List.range 4,BaseCheckAt 20 (20+i):=by decide +kernel

theorem br20p6:∀ i ∈ List.range 4,BaseCheckAt 20 (24+i):=by decide +kernel

theorem br20p7:∀ i ∈ List.range 4,BaseCheckAt 20 (28+i):=by decide +kernel

theorem br20p8:∀ i ∈ List.range 4,BaseCheckAt 20 (32+i):=by decide +kernel

theorem br20p9:∀ i ∈ List.range 4,BaseCheckAt 20 (36+i):=by decide +kernel

theorem br20p10:∀ i ∈ List.range 4,BaseCheckAt 20 (40+i):=by decide +kernel

theorem br20p11:∀ i ∈ List.range 4,BaseCheckAt 20 (44+i):=by decide +kernel

theorem br20p12:∀ i ∈ List.range 4,BaseCheckAt 20 (48+i):=by decide +kernel

theorem br20p13:∀ i ∈ List.range 4,BaseCheckAt 20 (52+i):=by decide +kernel

theorem br20p14:∀ i ∈ List.range 4,BaseCheckAt 20 (56+i):=by decide +kernel

theorem br20p15:∀ i ∈ List.range 4,BaseCheckAt 20 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
