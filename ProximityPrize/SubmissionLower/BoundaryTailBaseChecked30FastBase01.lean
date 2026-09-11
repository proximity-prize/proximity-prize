import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br30p0:∀ i ∈ List.range 4,BaseCheckAt 30 (0+i):=by decide +kernel

theorem br30p1:∀ i ∈ List.range 4,BaseCheckAt 30 (4+i):=by decide +kernel

theorem br30p2:∀ i ∈ List.range 4,BaseCheckAt 30 (8+i):=by decide +kernel

theorem br30p3:∀ i ∈ List.range 4,BaseCheckAt 30 (12+i):=by decide +kernel

theorem br30p4:∀ i ∈ List.range 4,BaseCheckAt 30 (16+i):=by decide +kernel

theorem br30p5:∀ i ∈ List.range 4,BaseCheckAt 30 (20+i):=by decide +kernel

theorem br30p6:∀ i ∈ List.range 4,BaseCheckAt 30 (24+i):=by decide +kernel

theorem br30p7:∀ i ∈ List.range 4,BaseCheckAt 30 (28+i):=by decide +kernel

theorem br30p8:∀ i ∈ List.range 4,BaseCheckAt 30 (32+i):=by decide +kernel

theorem br30p9:∀ i ∈ List.range 4,BaseCheckAt 30 (36+i):=by decide +kernel

theorem br30p10:∀ i ∈ List.range 4,BaseCheckAt 30 (40+i):=by decide +kernel

theorem br30p11:∀ i ∈ List.range 4,BaseCheckAt 30 (44+i):=by decide +kernel

theorem br30p12:∀ i ∈ List.range 4,BaseCheckAt 30 (48+i):=by decide +kernel

theorem br30p13:∀ i ∈ List.range 4,BaseCheckAt 30 (52+i):=by decide +kernel

theorem br30p14:∀ i ∈ List.range 4,BaseCheckAt 30 (56+i):=by decide +kernel

theorem br30p15:∀ i ∈ List.range 4,BaseCheckAt 30 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
