import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked12FastStrict09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br12p0:∀ i ∈ List.range 4,BaseCheckAt 12 (0+i):=by decide +kernel

theorem br12p1:∀ i ∈ List.range 4,BaseCheckAt 12 (4+i):=by decide +kernel

theorem br12p2:∀ i ∈ List.range 4,BaseCheckAt 12 (8+i):=by decide +kernel

theorem br12p3:∀ i ∈ List.range 4,BaseCheckAt 12 (12+i):=by decide +kernel

theorem br12p4:∀ i ∈ List.range 4,BaseCheckAt 12 (16+i):=by decide +kernel

theorem br12p5:∀ i ∈ List.range 4,BaseCheckAt 12 (20+i):=by decide +kernel

theorem br12p6:∀ i ∈ List.range 4,BaseCheckAt 12 (24+i):=by decide +kernel

theorem br12p7:∀ i ∈ List.range 4,BaseCheckAt 12 (28+i):=by decide +kernel

theorem br12p8:∀ i ∈ List.range 4,BaseCheckAt 12 (32+i):=by decide +kernel

theorem br12p9:∀ i ∈ List.range 4,BaseCheckAt 12 (36+i):=by decide +kernel

theorem br12p10:∀ i ∈ List.range 4,BaseCheckAt 12 (40+i):=by decide +kernel

theorem br12p11:∀ i ∈ List.range 4,BaseCheckAt 12 (44+i):=by decide +kernel

theorem br12p12:∀ i ∈ List.range 4,BaseCheckAt 12 (48+i):=by decide +kernel

theorem br12p13:∀ i ∈ List.range 4,BaseCheckAt 12 (52+i):=by decide +kernel

theorem br12p14:∀ i ∈ List.range 4,BaseCheckAt 12 (56+i):=by decide +kernel

theorem br12p15:∀ i ∈ List.range 4,BaseCheckAt 12 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
