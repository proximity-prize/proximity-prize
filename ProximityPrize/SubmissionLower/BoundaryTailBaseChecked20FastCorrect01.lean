import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked19

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr20p0:∀ i ∈ List.range 8,CorrectAt 20 (0+i):=by decide +kernel

theorem cr20p1:∀ i ∈ List.range 8,CorrectAt 20 (8+i):=by decide +kernel

theorem cr20p2:∀ i ∈ List.range 8,CorrectAt 20 (16+i):=by decide +kernel

theorem cr20p3:∀ i ∈ List.range 8,CorrectAt 20 (24+i):=by decide +kernel

theorem cr20p4:∀ i ∈ List.range 8,CorrectAt 20 (32+i):=by decide +kernel

theorem cr20p5:∀ i ∈ List.range 8,CorrectAt 20 (40+i):=by decide +kernel

theorem cr20p6:∀ i ∈ List.range 8,CorrectAt 20 (48+i):=by decide +kernel

theorem cr20p7:∀ i ∈ List.range 8,CorrectAt 20 (56+i):=by decide +kernel

theorem cr20p8:∀ i ∈ List.range 8,CorrectAt 20 (64+i):=by decide +kernel

theorem cr20p9:∀ i ∈ List.range 8,CorrectAt 20 (72+i):=by decide +kernel

theorem cr20p10:∀ i ∈ List.range 8,CorrectAt 20 (80+i):=by decide +kernel

theorem cr20p11:∀ i ∈ List.range 8,CorrectAt 20 (88+i):=by decide +kernel

theorem cr20p12:∀ i ∈ List.range 8,CorrectAt 20 (96+i):=by decide +kernel

theorem cr20p13:∀ i ∈ List.range 8,CorrectAt 20 (104+i):=by decide +kernel

theorem cr20p14:∀ i ∈ List.range 8,CorrectAt 20 (112+i):=by decide +kernel

theorem cr20p15:∀ i ∈ List.range 3,CorrectAt 20 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
