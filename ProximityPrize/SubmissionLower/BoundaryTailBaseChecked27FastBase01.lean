import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br27p0:∀ i ∈ List.range 4,BaseCheckAt 27 (0+i):=by decide +kernel

theorem br27p1:∀ i ∈ List.range 4,BaseCheckAt 27 (4+i):=by decide +kernel

theorem br27p2:∀ i ∈ List.range 4,BaseCheckAt 27 (8+i):=by decide +kernel

theorem br27p3:∀ i ∈ List.range 4,BaseCheckAt 27 (12+i):=by decide +kernel

theorem br27p4:∀ i ∈ List.range 4,BaseCheckAt 27 (16+i):=by decide +kernel

theorem br27p5:∀ i ∈ List.range 4,BaseCheckAt 27 (20+i):=by decide +kernel

theorem br27p6:∀ i ∈ List.range 4,BaseCheckAt 27 (24+i):=by decide +kernel

theorem br27p7:∀ i ∈ List.range 4,BaseCheckAt 27 (28+i):=by decide +kernel

theorem br27p8:∀ i ∈ List.range 4,BaseCheckAt 27 (32+i):=by decide +kernel

theorem br27p9:∀ i ∈ List.range 4,BaseCheckAt 27 (36+i):=by decide +kernel

theorem br27p10:∀ i ∈ List.range 4,BaseCheckAt 27 (40+i):=by decide +kernel

theorem br27p11:∀ i ∈ List.range 4,BaseCheckAt 27 (44+i):=by decide +kernel

theorem br27p12:∀ i ∈ List.range 4,BaseCheckAt 27 (48+i):=by decide +kernel

theorem br27p13:∀ i ∈ List.range 4,BaseCheckAt 27 (52+i):=by decide +kernel

theorem br27p14:∀ i ∈ List.range 4,BaseCheckAt 27 (56+i):=by decide +kernel

theorem br27p15:∀ i ∈ List.range 4,BaseCheckAt 27 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
