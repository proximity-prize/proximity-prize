import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked26FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br26p0:∀ i ∈ List.range 4,BaseCheckAt 26 (0+i):=by decide +kernel

theorem br26p1:∀ i ∈ List.range 4,BaseCheckAt 26 (4+i):=by decide +kernel

theorem br26p2:∀ i ∈ List.range 4,BaseCheckAt 26 (8+i):=by decide +kernel

theorem br26p3:∀ i ∈ List.range 4,BaseCheckAt 26 (12+i):=by decide +kernel

theorem br26p4:∀ i ∈ List.range 4,BaseCheckAt 26 (16+i):=by decide +kernel

theorem br26p5:∀ i ∈ List.range 4,BaseCheckAt 26 (20+i):=by decide +kernel

theorem br26p6:∀ i ∈ List.range 4,BaseCheckAt 26 (24+i):=by decide +kernel

theorem br26p7:∀ i ∈ List.range 4,BaseCheckAt 26 (28+i):=by decide +kernel

theorem br26p8:∀ i ∈ List.range 4,BaseCheckAt 26 (32+i):=by decide +kernel

theorem br26p9:∀ i ∈ List.range 4,BaseCheckAt 26 (36+i):=by decide +kernel

theorem br26p10:∀ i ∈ List.range 4,BaseCheckAt 26 (40+i):=by decide +kernel

theorem br26p11:∀ i ∈ List.range 4,BaseCheckAt 26 (44+i):=by decide +kernel

theorem br26p12:∀ i ∈ List.range 4,BaseCheckAt 26 (48+i):=by decide +kernel

theorem br26p13:∀ i ∈ List.range 4,BaseCheckAt 26 (52+i):=by decide +kernel

theorem br26p14:∀ i ∈ List.range 4,BaseCheckAt 26 (56+i):=by decide +kernel

theorem br26p15:∀ i ∈ List.range 4,BaseCheckAt 26 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
