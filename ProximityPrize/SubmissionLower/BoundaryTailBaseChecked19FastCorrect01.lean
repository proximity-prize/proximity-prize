import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked18

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr19p0:∀ i ∈ List.range 8,CorrectAt 19 (0+i):=by decide +kernel

theorem cr19p1:∀ i ∈ List.range 8,CorrectAt 19 (8+i):=by decide +kernel

theorem cr19p2:∀ i ∈ List.range 8,CorrectAt 19 (16+i):=by decide +kernel

theorem cr19p3:∀ i ∈ List.range 8,CorrectAt 19 (24+i):=by decide +kernel

theorem cr19p4:∀ i ∈ List.range 8,CorrectAt 19 (32+i):=by decide +kernel

theorem cr19p5:∀ i ∈ List.range 8,CorrectAt 19 (40+i):=by decide +kernel

theorem cr19p6:∀ i ∈ List.range 8,CorrectAt 19 (48+i):=by decide +kernel

theorem cr19p7:∀ i ∈ List.range 8,CorrectAt 19 (56+i):=by decide +kernel

theorem cr19p8:∀ i ∈ List.range 8,CorrectAt 19 (64+i):=by decide +kernel

theorem cr19p9:∀ i ∈ List.range 8,CorrectAt 19 (72+i):=by decide +kernel

theorem cr19p10:∀ i ∈ List.range 8,CorrectAt 19 (80+i):=by decide +kernel

theorem cr19p11:∀ i ∈ List.range 8,CorrectAt 19 (88+i):=by decide +kernel

theorem cr19p12:∀ i ∈ List.range 8,CorrectAt 19 (96+i):=by decide +kernel

theorem cr19p13:∀ i ∈ List.range 8,CorrectAt 19 (104+i):=by decide +kernel

theorem cr19p14:∀ i ∈ List.range 8,CorrectAt 19 (112+i):=by decide +kernel

theorem cr19p15:∀ i ∈ List.range 4,CorrectAt 19 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
