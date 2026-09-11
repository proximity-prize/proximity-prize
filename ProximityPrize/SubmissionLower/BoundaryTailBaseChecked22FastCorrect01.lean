import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked21

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr22p0:∀ i ∈ List.range 8,CorrectAt 22 (0+i):=by decide +kernel

theorem cr22p1:∀ i ∈ List.range 8,CorrectAt 22 (8+i):=by decide +kernel

theorem cr22p2:∀ i ∈ List.range 8,CorrectAt 22 (16+i):=by decide +kernel

theorem cr22p3:∀ i ∈ List.range 8,CorrectAt 22 (24+i):=by decide +kernel

theorem cr22p4:∀ i ∈ List.range 8,CorrectAt 22 (32+i):=by decide +kernel

theorem cr22p5:∀ i ∈ List.range 8,CorrectAt 22 (40+i):=by decide +kernel

theorem cr22p6:∀ i ∈ List.range 8,CorrectAt 22 (48+i):=by decide +kernel

theorem cr22p7:∀ i ∈ List.range 8,CorrectAt 22 (56+i):=by decide +kernel

theorem cr22p8:∀ i ∈ List.range 8,CorrectAt 22 (64+i):=by decide +kernel

theorem cr22p9:∀ i ∈ List.range 8,CorrectAt 22 (72+i):=by decide +kernel

theorem cr22p10:∀ i ∈ List.range 8,CorrectAt 22 (80+i):=by decide +kernel

theorem cr22p11:∀ i ∈ List.range 8,CorrectAt 22 (88+i):=by decide +kernel

theorem cr22p12:∀ i ∈ List.range 8,CorrectAt 22 (96+i):=by decide +kernel

theorem cr22p13:∀ i ∈ List.range 8,CorrectAt 22 (104+i):=by decide +kernel

theorem cr22p14:∀ i ∈ List.range 8,CorrectAt 22 (112+i):=by decide +kernel

theorem cr22p15:∀ i ∈ List.range 1,CorrectAt 22 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
