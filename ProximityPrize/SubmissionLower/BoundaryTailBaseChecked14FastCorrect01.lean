import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked13

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr14p0:∀ i ∈ List.range 8,CorrectAt 14 (0+i):=by decide +kernel

theorem cr14p1:∀ i ∈ List.range 8,CorrectAt 14 (8+i):=by decide +kernel

theorem cr14p2:∀ i ∈ List.range 8,CorrectAt 14 (16+i):=by decide +kernel

theorem cr14p3:∀ i ∈ List.range 8,CorrectAt 14 (24+i):=by decide +kernel

theorem cr14p4:∀ i ∈ List.range 8,CorrectAt 14 (32+i):=by decide +kernel

theorem cr14p5:∀ i ∈ List.range 8,CorrectAt 14 (40+i):=by decide +kernel

theorem cr14p6:∀ i ∈ List.range 8,CorrectAt 14 (48+i):=by decide +kernel

theorem cr14p7:∀ i ∈ List.range 8,CorrectAt 14 (56+i):=by decide +kernel

theorem cr14p8:∀ i ∈ List.range 8,CorrectAt 14 (64+i):=by decide +kernel

theorem cr14p9:∀ i ∈ List.range 8,CorrectAt 14 (72+i):=by decide +kernel

theorem cr14p10:∀ i ∈ List.range 8,CorrectAt 14 (80+i):=by decide +kernel

theorem cr14p11:∀ i ∈ List.range 8,CorrectAt 14 (88+i):=by decide +kernel

theorem cr14p12:∀ i ∈ List.range 8,CorrectAt 14 (96+i):=by decide +kernel

theorem cr14p13:∀ i ∈ List.range 8,CorrectAt 14 (104+i):=by decide +kernel

theorem cr14p14:∀ i ∈ List.range 8,CorrectAt 14 (112+i):=by decide +kernel

theorem cr14p15:∀ i ∈ List.range 8,CorrectAt 14 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
