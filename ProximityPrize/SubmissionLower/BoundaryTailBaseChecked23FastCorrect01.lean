import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked22

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr23p0:∀ i ∈ List.range 8,CorrectAt 23 (0+i):=by decide +kernel

theorem cr23p1:∀ i ∈ List.range 8,CorrectAt 23 (8+i):=by decide +kernel

theorem cr23p2:∀ i ∈ List.range 8,CorrectAt 23 (16+i):=by decide +kernel

theorem cr23p3:∀ i ∈ List.range 8,CorrectAt 23 (24+i):=by decide +kernel

theorem cr23p4:∀ i ∈ List.range 8,CorrectAt 23 (32+i):=by decide +kernel

theorem cr23p5:∀ i ∈ List.range 8,CorrectAt 23 (40+i):=by decide +kernel

theorem cr23p6:∀ i ∈ List.range 8,CorrectAt 23 (48+i):=by decide +kernel

theorem cr23p7:∀ i ∈ List.range 8,CorrectAt 23 (56+i):=by decide +kernel

theorem cr23p8:∀ i ∈ List.range 8,CorrectAt 23 (64+i):=by decide +kernel

theorem cr23p9:∀ i ∈ List.range 8,CorrectAt 23 (72+i):=by decide +kernel

theorem cr23p10:∀ i ∈ List.range 8,CorrectAt 23 (80+i):=by decide +kernel

theorem cr23p11:∀ i ∈ List.range 8,CorrectAt 23 (88+i):=by decide +kernel

theorem cr23p12:∀ i ∈ List.range 8,CorrectAt 23 (96+i):=by decide +kernel

theorem cr23p13:∀ i ∈ List.range 8,CorrectAt 23 (104+i):=by decide +kernel

theorem cr23p14:∀ i ∈ List.range 8,CorrectAt 23 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
