import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked16

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr17p0:∀ i ∈ List.range 8,CorrectAt 17 (0+i):=by decide +kernel

theorem cr17p1:∀ i ∈ List.range 8,CorrectAt 17 (8+i):=by decide +kernel

theorem cr17p2:∀ i ∈ List.range 8,CorrectAt 17 (16+i):=by decide +kernel

theorem cr17p3:∀ i ∈ List.range 8,CorrectAt 17 (24+i):=by decide +kernel

theorem cr17p4:∀ i ∈ List.range 8,CorrectAt 17 (32+i):=by decide +kernel

theorem cr17p5:∀ i ∈ List.range 8,CorrectAt 17 (40+i):=by decide +kernel

theorem cr17p6:∀ i ∈ List.range 8,CorrectAt 17 (48+i):=by decide +kernel

theorem cr17p7:∀ i ∈ List.range 8,CorrectAt 17 (56+i):=by decide +kernel

theorem cr17p8:∀ i ∈ List.range 8,CorrectAt 17 (64+i):=by decide +kernel

theorem cr17p9:∀ i ∈ List.range 8,CorrectAt 17 (72+i):=by decide +kernel

theorem cr17p10:∀ i ∈ List.range 8,CorrectAt 17 (80+i):=by decide +kernel

theorem cr17p11:∀ i ∈ List.range 8,CorrectAt 17 (88+i):=by decide +kernel

theorem cr17p12:∀ i ∈ List.range 8,CorrectAt 17 (96+i):=by decide +kernel

theorem cr17p13:∀ i ∈ List.range 8,CorrectAt 17 (104+i):=by decide +kernel

theorem cr17p14:∀ i ∈ List.range 8,CorrectAt 17 (112+i):=by decide +kernel

theorem cr17p15:∀ i ∈ List.range 6,CorrectAt 17 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
