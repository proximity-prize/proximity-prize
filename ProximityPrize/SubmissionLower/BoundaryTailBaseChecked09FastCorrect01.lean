import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr9p0:∀ i ∈ List.range 8,CorrectAt 9 (0+i):=by decide +kernel

theorem cr9p1:∀ i ∈ List.range 8,CorrectAt 9 (8+i):=by decide +kernel

theorem cr9p2:∀ i ∈ List.range 8,CorrectAt 9 (16+i):=by decide +kernel

theorem cr9p3:∀ i ∈ List.range 8,CorrectAt 9 (24+i):=by decide +kernel

theorem cr9p4:∀ i ∈ List.range 8,CorrectAt 9 (32+i):=by decide +kernel

theorem cr9p5:∀ i ∈ List.range 8,CorrectAt 9 (40+i):=by decide +kernel

theorem cr9p6:∀ i ∈ List.range 8,CorrectAt 9 (48+i):=by decide +kernel

theorem cr9p7:∀ i ∈ List.range 8,CorrectAt 9 (56+i):=by decide +kernel

theorem cr9p8:∀ i ∈ List.range 8,CorrectAt 9 (64+i):=by decide +kernel

theorem cr9p9:∀ i ∈ List.range 8,CorrectAt 9 (72+i):=by decide +kernel

theorem cr9p10:∀ i ∈ List.range 8,CorrectAt 9 (80+i):=by decide +kernel

theorem cr9p11:∀ i ∈ List.range 8,CorrectAt 9 (88+i):=by decide +kernel

theorem cr9p12:∀ i ∈ List.range 8,CorrectAt 9 (96+i):=by decide +kernel

theorem cr9p13:∀ i ∈ List.range 8,CorrectAt 9 (104+i):=by decide +kernel

theorem cr9p14:∀ i ∈ List.range 8,CorrectAt 9 (112+i):=by decide +kernel

theorem cr9p15:∀ i ∈ List.range 8,CorrectAt 9 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
