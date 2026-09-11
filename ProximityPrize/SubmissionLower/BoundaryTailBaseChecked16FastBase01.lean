import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br16p0:∀ i ∈ List.range 4,BaseCheckAt 16 (0+i):=by decide +kernel

theorem br16p1:∀ i ∈ List.range 4,BaseCheckAt 16 (4+i):=by decide +kernel

theorem br16p2:∀ i ∈ List.range 4,BaseCheckAt 16 (8+i):=by decide +kernel

theorem br16p3:∀ i ∈ List.range 4,BaseCheckAt 16 (12+i):=by decide +kernel

theorem br16p4:∀ i ∈ List.range 4,BaseCheckAt 16 (16+i):=by decide +kernel

theorem br16p5:∀ i ∈ List.range 4,BaseCheckAt 16 (20+i):=by decide +kernel

theorem br16p6:∀ i ∈ List.range 4,BaseCheckAt 16 (24+i):=by decide +kernel

theorem br16p7:∀ i ∈ List.range 4,BaseCheckAt 16 (28+i):=by decide +kernel

theorem br16p8:∀ i ∈ List.range 4,BaseCheckAt 16 (32+i):=by decide +kernel

theorem br16p9:∀ i ∈ List.range 4,BaseCheckAt 16 (36+i):=by decide +kernel

theorem br16p10:∀ i ∈ List.range 4,BaseCheckAt 16 (40+i):=by decide +kernel

theorem br16p11:∀ i ∈ List.range 4,BaseCheckAt 16 (44+i):=by decide +kernel

theorem br16p12:∀ i ∈ List.range 4,BaseCheckAt 16 (48+i):=by decide +kernel

theorem br16p13:∀ i ∈ List.range 4,BaseCheckAt 16 (52+i):=by decide +kernel

theorem br16p14:∀ i ∈ List.range 4,BaseCheckAt 16 (56+i):=by decide +kernel

theorem br16p15:∀ i ∈ List.range 4,BaseCheckAt 16 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
