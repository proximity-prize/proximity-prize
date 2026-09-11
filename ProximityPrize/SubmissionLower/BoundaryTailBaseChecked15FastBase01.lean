import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br15p0:∀ i ∈ List.range 4,BaseCheckAt 15 (0+i):=by decide +kernel

theorem br15p1:∀ i ∈ List.range 4,BaseCheckAt 15 (4+i):=by decide +kernel

theorem br15p2:∀ i ∈ List.range 4,BaseCheckAt 15 (8+i):=by decide +kernel

theorem br15p3:∀ i ∈ List.range 4,BaseCheckAt 15 (12+i):=by decide +kernel

theorem br15p4:∀ i ∈ List.range 4,BaseCheckAt 15 (16+i):=by decide +kernel

theorem br15p5:∀ i ∈ List.range 4,BaseCheckAt 15 (20+i):=by decide +kernel

theorem br15p6:∀ i ∈ List.range 4,BaseCheckAt 15 (24+i):=by decide +kernel

theorem br15p7:∀ i ∈ List.range 4,BaseCheckAt 15 (28+i):=by decide +kernel

theorem br15p8:∀ i ∈ List.range 4,BaseCheckAt 15 (32+i):=by decide +kernel

theorem br15p9:∀ i ∈ List.range 4,BaseCheckAt 15 (36+i):=by decide +kernel

theorem br15p10:∀ i ∈ List.range 4,BaseCheckAt 15 (40+i):=by decide +kernel

theorem br15p11:∀ i ∈ List.range 4,BaseCheckAt 15 (44+i):=by decide +kernel

theorem br15p12:∀ i ∈ List.range 4,BaseCheckAt 15 (48+i):=by decide +kernel

theorem br15p13:∀ i ∈ List.range 4,BaseCheckAt 15 (52+i):=by decide +kernel

theorem br15p14:∀ i ∈ List.range 4,BaseCheckAt 15 (56+i):=by decide +kernel

theorem br15p15:∀ i ∈ List.range 4,BaseCheckAt 15 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
