import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked20

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr21p0:∀ i ∈ List.range 8,CorrectAt 21 (0+i):=by decide +kernel

theorem cr21p1:∀ i ∈ List.range 8,CorrectAt 21 (8+i):=by decide +kernel

theorem cr21p2:∀ i ∈ List.range 8,CorrectAt 21 (16+i):=by decide +kernel

theorem cr21p3:∀ i ∈ List.range 8,CorrectAt 21 (24+i):=by decide +kernel

theorem cr21p4:∀ i ∈ List.range 8,CorrectAt 21 (32+i):=by decide +kernel

theorem cr21p5:∀ i ∈ List.range 8,CorrectAt 21 (40+i):=by decide +kernel

theorem cr21p6:∀ i ∈ List.range 8,CorrectAt 21 (48+i):=by decide +kernel

theorem cr21p7:∀ i ∈ List.range 8,CorrectAt 21 (56+i):=by decide +kernel

theorem cr21p8:∀ i ∈ List.range 8,CorrectAt 21 (64+i):=by decide +kernel

theorem cr21p9:∀ i ∈ List.range 8,CorrectAt 21 (72+i):=by decide +kernel

theorem cr21p10:∀ i ∈ List.range 8,CorrectAt 21 (80+i):=by decide +kernel

theorem cr21p11:∀ i ∈ List.range 8,CorrectAt 21 (88+i):=by decide +kernel

theorem cr21p12:∀ i ∈ List.range 8,CorrectAt 21 (96+i):=by decide +kernel

theorem cr21p13:∀ i ∈ List.range 8,CorrectAt 21 (104+i):=by decide +kernel

theorem cr21p14:∀ i ∈ List.range 8,CorrectAt 21 (112+i):=by decide +kernel

theorem cr21p15:∀ i ∈ List.range 2,CorrectAt 21 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
