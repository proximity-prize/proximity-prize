import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked15

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr16p0:∀ i ∈ List.range 8,CorrectAt 16 (0+i):=by decide +kernel

theorem cr16p1:∀ i ∈ List.range 8,CorrectAt 16 (8+i):=by decide +kernel

theorem cr16p2:∀ i ∈ List.range 8,CorrectAt 16 (16+i):=by decide +kernel

theorem cr16p3:∀ i ∈ List.range 8,CorrectAt 16 (24+i):=by decide +kernel

theorem cr16p4:∀ i ∈ List.range 8,CorrectAt 16 (32+i):=by decide +kernel

theorem cr16p5:∀ i ∈ List.range 8,CorrectAt 16 (40+i):=by decide +kernel

theorem cr16p6:∀ i ∈ List.range 8,CorrectAt 16 (48+i):=by decide +kernel

theorem cr16p7:∀ i ∈ List.range 8,CorrectAt 16 (56+i):=by decide +kernel

theorem cr16p8:∀ i ∈ List.range 8,CorrectAt 16 (64+i):=by decide +kernel

theorem cr16p9:∀ i ∈ List.range 8,CorrectAt 16 (72+i):=by decide +kernel

theorem cr16p10:∀ i ∈ List.range 8,CorrectAt 16 (80+i):=by decide +kernel

theorem cr16p11:∀ i ∈ List.range 8,CorrectAt 16 (88+i):=by decide +kernel

theorem cr16p12:∀ i ∈ List.range 8,CorrectAt 16 (96+i):=by decide +kernel

theorem cr16p13:∀ i ∈ List.range 8,CorrectAt 16 (104+i):=by decide +kernel

theorem cr16p14:∀ i ∈ List.range 8,CorrectAt 16 (112+i):=by decide +kernel

theorem cr16p15:∀ i ∈ List.range 7,CorrectAt 16 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
