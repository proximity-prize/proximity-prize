import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastZero07
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked31FastStrict07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br31p0:∀ i ∈ List.range 4,BaseCheckAt 31 (0+i):=by decide +kernel

theorem br31p1:∀ i ∈ List.range 4,BaseCheckAt 31 (4+i):=by decide +kernel

theorem br31p2:∀ i ∈ List.range 4,BaseCheckAt 31 (8+i):=by decide +kernel

theorem br31p3:∀ i ∈ List.range 4,BaseCheckAt 31 (12+i):=by decide +kernel

theorem br31p4:∀ i ∈ List.range 4,BaseCheckAt 31 (16+i):=by decide +kernel

theorem br31p5:∀ i ∈ List.range 4,BaseCheckAt 31 (20+i):=by decide +kernel

theorem br31p6:∀ i ∈ List.range 4,BaseCheckAt 31 (24+i):=by decide +kernel

theorem br31p7:∀ i ∈ List.range 4,BaseCheckAt 31 (28+i):=by decide +kernel

theorem br31p8:∀ i ∈ List.range 4,BaseCheckAt 31 (32+i):=by decide +kernel

theorem br31p9:∀ i ∈ List.range 4,BaseCheckAt 31 (36+i):=by decide +kernel

theorem br31p10:∀ i ∈ List.range 4,BaseCheckAt 31 (40+i):=by decide +kernel

theorem br31p11:∀ i ∈ List.range 4,BaseCheckAt 31 (44+i):=by decide +kernel

theorem br31p12:∀ i ∈ List.range 4,BaseCheckAt 31 (48+i):=by decide +kernel

theorem br31p13:∀ i ∈ List.range 4,BaseCheckAt 31 (52+i):=by decide +kernel

theorem br31p14:∀ i ∈ List.range 4,BaseCheckAt 31 (56+i):=by decide +kernel

theorem br31p15:∀ i ∈ List.range 4,BaseCheckAt 31 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
