import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked14

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr15p0:∀ i ∈ List.range 8,CorrectAt 15 (0+i):=by decide +kernel

theorem cr15p1:∀ i ∈ List.range 8,CorrectAt 15 (8+i):=by decide +kernel

theorem cr15p2:∀ i ∈ List.range 8,CorrectAt 15 (16+i):=by decide +kernel

theorem cr15p3:∀ i ∈ List.range 8,CorrectAt 15 (24+i):=by decide +kernel

theorem cr15p4:∀ i ∈ List.range 8,CorrectAt 15 (32+i):=by decide +kernel

theorem cr15p5:∀ i ∈ List.range 8,CorrectAt 15 (40+i):=by decide +kernel

theorem cr15p6:∀ i ∈ List.range 8,CorrectAt 15 (48+i):=by decide +kernel

theorem cr15p7:∀ i ∈ List.range 8,CorrectAt 15 (56+i):=by decide +kernel

theorem cr15p8:∀ i ∈ List.range 8,CorrectAt 15 (64+i):=by decide +kernel

theorem cr15p9:∀ i ∈ List.range 8,CorrectAt 15 (72+i):=by decide +kernel

theorem cr15p10:∀ i ∈ List.range 8,CorrectAt 15 (80+i):=by decide +kernel

theorem cr15p11:∀ i ∈ List.range 8,CorrectAt 15 (88+i):=by decide +kernel

theorem cr15p12:∀ i ∈ List.range 8,CorrectAt 15 (96+i):=by decide +kernel

theorem cr15p13:∀ i ∈ List.range 8,CorrectAt 15 (104+i):=by decide +kernel

theorem cr15p14:∀ i ∈ List.range 8,CorrectAt 15 (112+i):=by decide +kernel

theorem cr15p15:∀ i ∈ List.range 8,CorrectAt 15 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
