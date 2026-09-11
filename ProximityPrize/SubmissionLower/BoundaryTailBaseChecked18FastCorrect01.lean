import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked17

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr18p0:∀ i ∈ List.range 8,CorrectAt 18 (0+i):=by decide +kernel

theorem cr18p1:∀ i ∈ List.range 8,CorrectAt 18 (8+i):=by decide +kernel

theorem cr18p2:∀ i ∈ List.range 8,CorrectAt 18 (16+i):=by decide +kernel

theorem cr18p3:∀ i ∈ List.range 8,CorrectAt 18 (24+i):=by decide +kernel

theorem cr18p4:∀ i ∈ List.range 8,CorrectAt 18 (32+i):=by decide +kernel

theorem cr18p5:∀ i ∈ List.range 8,CorrectAt 18 (40+i):=by decide +kernel

theorem cr18p6:∀ i ∈ List.range 8,CorrectAt 18 (48+i):=by decide +kernel

theorem cr18p7:∀ i ∈ List.range 8,CorrectAt 18 (56+i):=by decide +kernel

theorem cr18p8:∀ i ∈ List.range 8,CorrectAt 18 (64+i):=by decide +kernel

theorem cr18p9:∀ i ∈ List.range 8,CorrectAt 18 (72+i):=by decide +kernel

theorem cr18p10:∀ i ∈ List.range 8,CorrectAt 18 (80+i):=by decide +kernel

theorem cr18p11:∀ i ∈ List.range 8,CorrectAt 18 (88+i):=by decide +kernel

theorem cr18p12:∀ i ∈ List.range 8,CorrectAt 18 (96+i):=by decide +kernel

theorem cr18p13:∀ i ∈ List.range 8,CorrectAt 18 (104+i):=by decide +kernel

theorem cr18p14:∀ i ∈ List.range 8,CorrectAt 18 (112+i):=by decide +kernel

theorem cr18p15:∀ i ∈ List.range 5,CorrectAt 18 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
