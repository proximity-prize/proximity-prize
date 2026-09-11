import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked06
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastData
import ProximityPrize.SubmissionLower.BoundaryTailBaseFastValidated

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr7p0:∀ i ∈ List.range 8,CorrectAt 7 (0+i):=by decide +kernel

theorem cr7p1:∀ i ∈ List.range 8,CorrectAt 7 (8+i):=by decide +kernel

theorem cr7p2:∀ i ∈ List.range 8,CorrectAt 7 (16+i):=by decide +kernel

theorem cr7p3:∀ i ∈ List.range 8,CorrectAt 7 (24+i):=by decide +kernel

theorem cr7p4:∀ i ∈ List.range 8,CorrectAt 7 (32+i):=by decide +kernel

theorem cr7p5:∀ i ∈ List.range 8,CorrectAt 7 (40+i):=by decide +kernel

theorem cr7p6:∀ i ∈ List.range 8,CorrectAt 7 (48+i):=by decide +kernel

theorem cr7p7:∀ i ∈ List.range 8,CorrectAt 7 (56+i):=by decide +kernel

theorem cr7p8:∀ i ∈ List.range 8,CorrectAt 7 (64+i):=by decide +kernel

theorem cr7p9:∀ i ∈ List.range 8,CorrectAt 7 (72+i):=by decide +kernel

theorem cr7p10:∀ i ∈ List.range 8,CorrectAt 7 (80+i):=by decide +kernel

theorem cr7p11:∀ i ∈ List.range 8,CorrectAt 7 (88+i):=by decide +kernel

theorem cr7p12:∀ i ∈ List.range 8,CorrectAt 7 (96+i):=by decide +kernel

theorem cr7p13:∀ i ∈ List.range 8,CorrectAt 7 (104+i):=by decide +kernel

theorem cr7p14:∀ i ∈ List.range 8,CorrectAt 7 (112+i):=by decide +kernel

theorem cr7p15:∀ i ∈ List.range 8,CorrectAt 7 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
