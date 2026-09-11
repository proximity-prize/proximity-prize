import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked11

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr12p0:∀ i ∈ List.range 8,CorrectAt 12 (0+i):=by decide +kernel

theorem cr12p1:∀ i ∈ List.range 8,CorrectAt 12 (8+i):=by decide +kernel

theorem cr12p2:∀ i ∈ List.range 8,CorrectAt 12 (16+i):=by decide +kernel

theorem cr12p3:∀ i ∈ List.range 8,CorrectAt 12 (24+i):=by decide +kernel

theorem cr12p4:∀ i ∈ List.range 8,CorrectAt 12 (32+i):=by decide +kernel

theorem cr12p5:∀ i ∈ List.range 8,CorrectAt 12 (40+i):=by decide +kernel

theorem cr12p6:∀ i ∈ List.range 8,CorrectAt 12 (48+i):=by decide +kernel

theorem cr12p7:∀ i ∈ List.range 8,CorrectAt 12 (56+i):=by decide +kernel

theorem cr12p8:∀ i ∈ List.range 8,CorrectAt 12 (64+i):=by decide +kernel

theorem cr12p9:∀ i ∈ List.range 8,CorrectAt 12 (72+i):=by decide +kernel

theorem cr12p10:∀ i ∈ List.range 8,CorrectAt 12 (80+i):=by decide +kernel

theorem cr12p11:∀ i ∈ List.range 8,CorrectAt 12 (88+i):=by decide +kernel

theorem cr12p12:∀ i ∈ List.range 8,CorrectAt 12 (96+i):=by decide +kernel

theorem cr12p13:∀ i ∈ List.range 8,CorrectAt 12 (104+i):=by decide +kernel

theorem cr12p14:∀ i ∈ List.range 8,CorrectAt 12 (112+i):=by decide +kernel

theorem cr12p15:∀ i ∈ List.range 8,CorrectAt 12 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
