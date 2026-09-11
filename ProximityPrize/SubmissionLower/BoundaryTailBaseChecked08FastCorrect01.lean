import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked07

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr8p0:∀ i ∈ List.range 8,CorrectAt 8 (0+i):=by decide +kernel

theorem cr8p1:∀ i ∈ List.range 8,CorrectAt 8 (8+i):=by decide +kernel

theorem cr8p2:∀ i ∈ List.range 8,CorrectAt 8 (16+i):=by decide +kernel

theorem cr8p3:∀ i ∈ List.range 8,CorrectAt 8 (24+i):=by decide +kernel

theorem cr8p4:∀ i ∈ List.range 8,CorrectAt 8 (32+i):=by decide +kernel

theorem cr8p5:∀ i ∈ List.range 8,CorrectAt 8 (40+i):=by decide +kernel

theorem cr8p6:∀ i ∈ List.range 8,CorrectAt 8 (48+i):=by decide +kernel

theorem cr8p7:∀ i ∈ List.range 8,CorrectAt 8 (56+i):=by decide +kernel

theorem cr8p8:∀ i ∈ List.range 8,CorrectAt 8 (64+i):=by decide +kernel

theorem cr8p9:∀ i ∈ List.range 8,CorrectAt 8 (72+i):=by decide +kernel

theorem cr8p10:∀ i ∈ List.range 8,CorrectAt 8 (80+i):=by decide +kernel

theorem cr8p11:∀ i ∈ List.range 8,CorrectAt 8 (88+i):=by decide +kernel

theorem cr8p12:∀ i ∈ List.range 8,CorrectAt 8 (96+i):=by decide +kernel

theorem cr8p13:∀ i ∈ List.range 8,CorrectAt 8 (104+i):=by decide +kernel

theorem cr8p14:∀ i ∈ List.range 8,CorrectAt 8 (112+i):=by decide +kernel

theorem cr8p15:∀ i ∈ List.range 8,CorrectAt 8 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
