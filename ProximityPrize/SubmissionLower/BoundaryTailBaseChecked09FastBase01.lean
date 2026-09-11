import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked09FastStrict09

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br9p0:∀ i ∈ List.range 4,BaseCheckAt 9 (0+i):=by decide +kernel

theorem br9p1:∀ i ∈ List.range 4,BaseCheckAt 9 (4+i):=by decide +kernel

theorem br9p2:∀ i ∈ List.range 4,BaseCheckAt 9 (8+i):=by decide +kernel

theorem br9p3:∀ i ∈ List.range 4,BaseCheckAt 9 (12+i):=by decide +kernel

theorem br9p4:∀ i ∈ List.range 4,BaseCheckAt 9 (16+i):=by decide +kernel

theorem br9p5:∀ i ∈ List.range 4,BaseCheckAt 9 (20+i):=by decide +kernel

theorem br9p6:∀ i ∈ List.range 4,BaseCheckAt 9 (24+i):=by decide +kernel

theorem br9p7:∀ i ∈ List.range 4,BaseCheckAt 9 (28+i):=by decide +kernel

theorem br9p8:∀ i ∈ List.range 4,BaseCheckAt 9 (32+i):=by decide +kernel

theorem br9p9:∀ i ∈ List.range 4,BaseCheckAt 9 (36+i):=by decide +kernel

theorem br9p10:∀ i ∈ List.range 4,BaseCheckAt 9 (40+i):=by decide +kernel

theorem br9p11:∀ i ∈ List.range 4,BaseCheckAt 9 (44+i):=by decide +kernel

theorem br9p12:∀ i ∈ List.range 4,BaseCheckAt 9 (48+i):=by decide +kernel

theorem br9p13:∀ i ∈ List.range 4,BaseCheckAt 9 (52+i):=by decide +kernel

theorem br9p14:∀ i ∈ List.range 4,BaseCheckAt 9 (56+i):=by decide +kernel

theorem br9p15:∀ i ∈ List.range 4,BaseCheckAt 9 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
