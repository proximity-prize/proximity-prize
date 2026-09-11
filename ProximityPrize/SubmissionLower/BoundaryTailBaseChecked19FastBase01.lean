import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br19p0:∀ i ∈ List.range 4,BaseCheckAt 19 (0+i):=by decide +kernel

theorem br19p1:∀ i ∈ List.range 4,BaseCheckAt 19 (4+i):=by decide +kernel

theorem br19p2:∀ i ∈ List.range 4,BaseCheckAt 19 (8+i):=by decide +kernel

theorem br19p3:∀ i ∈ List.range 4,BaseCheckAt 19 (12+i):=by decide +kernel

theorem br19p4:∀ i ∈ List.range 4,BaseCheckAt 19 (16+i):=by decide +kernel

theorem br19p5:∀ i ∈ List.range 4,BaseCheckAt 19 (20+i):=by decide +kernel

theorem br19p6:∀ i ∈ List.range 4,BaseCheckAt 19 (24+i):=by decide +kernel

theorem br19p7:∀ i ∈ List.range 4,BaseCheckAt 19 (28+i):=by decide +kernel

theorem br19p8:∀ i ∈ List.range 4,BaseCheckAt 19 (32+i):=by decide +kernel

theorem br19p9:∀ i ∈ List.range 4,BaseCheckAt 19 (36+i):=by decide +kernel

theorem br19p10:∀ i ∈ List.range 4,BaseCheckAt 19 (40+i):=by decide +kernel

theorem br19p11:∀ i ∈ List.range 4,BaseCheckAt 19 (44+i):=by decide +kernel

theorem br19p12:∀ i ∈ List.range 4,BaseCheckAt 19 (48+i):=by decide +kernel

theorem br19p13:∀ i ∈ List.range 4,BaseCheckAt 19 (52+i):=by decide +kernel

theorem br19p14:∀ i ∈ List.range 4,BaseCheckAt 19 (56+i):=by decide +kernel

theorem br19p15:∀ i ∈ List.range 4,BaseCheckAt 19 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
