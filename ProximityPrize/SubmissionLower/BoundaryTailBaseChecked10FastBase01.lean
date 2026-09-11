import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10FastStrict09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br10p0:∀ i ∈ List.range 4,BaseCheckAt 10 (0+i):=by decide +kernel

theorem br10p1:∀ i ∈ List.range 4,BaseCheckAt 10 (4+i):=by decide +kernel

theorem br10p2:∀ i ∈ List.range 4,BaseCheckAt 10 (8+i):=by decide +kernel

theorem br10p3:∀ i ∈ List.range 4,BaseCheckAt 10 (12+i):=by decide +kernel

theorem br10p4:∀ i ∈ List.range 4,BaseCheckAt 10 (16+i):=by decide +kernel

theorem br10p5:∀ i ∈ List.range 4,BaseCheckAt 10 (20+i):=by decide +kernel

theorem br10p6:∀ i ∈ List.range 4,BaseCheckAt 10 (24+i):=by decide +kernel

theorem br10p7:∀ i ∈ List.range 4,BaseCheckAt 10 (28+i):=by decide +kernel

theorem br10p8:∀ i ∈ List.range 4,BaseCheckAt 10 (32+i):=by decide +kernel

theorem br10p9:∀ i ∈ List.range 4,BaseCheckAt 10 (36+i):=by decide +kernel

theorem br10p10:∀ i ∈ List.range 4,BaseCheckAt 10 (40+i):=by decide +kernel

theorem br10p11:∀ i ∈ List.range 4,BaseCheckAt 10 (44+i):=by decide +kernel

theorem br10p12:∀ i ∈ List.range 4,BaseCheckAt 10 (48+i):=by decide +kernel

theorem br10p13:∀ i ∈ List.range 4,BaseCheckAt 10 (52+i):=by decide +kernel

theorem br10p14:∀ i ∈ List.range 4,BaseCheckAt 10 (56+i):=by decide +kernel

theorem br10p15:∀ i ∈ List.range 4,BaseCheckAt 10 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
