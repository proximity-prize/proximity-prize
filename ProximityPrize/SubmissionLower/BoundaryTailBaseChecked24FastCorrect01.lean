import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr24p0:∀ i ∈ List.range 8,CorrectAt 24 (0+i):=by decide +kernel

theorem cr24p1:∀ i ∈ List.range 8,CorrectAt 24 (8+i):=by decide +kernel

theorem cr24p2:∀ i ∈ List.range 8,CorrectAt 24 (16+i):=by decide +kernel

theorem cr24p3:∀ i ∈ List.range 8,CorrectAt 24 (24+i):=by decide +kernel

theorem cr24p4:∀ i ∈ List.range 8,CorrectAt 24 (32+i):=by decide +kernel

theorem cr24p5:∀ i ∈ List.range 8,CorrectAt 24 (40+i):=by decide +kernel

theorem cr24p6:∀ i ∈ List.range 8,CorrectAt 24 (48+i):=by decide +kernel

theorem cr24p7:∀ i ∈ List.range 8,CorrectAt 24 (56+i):=by decide +kernel

theorem cr24p8:∀ i ∈ List.range 8,CorrectAt 24 (64+i):=by decide +kernel

theorem cr24p9:∀ i ∈ List.range 8,CorrectAt 24 (72+i):=by decide +kernel

theorem cr24p10:∀ i ∈ List.range 8,CorrectAt 24 (80+i):=by decide +kernel

theorem cr24p11:∀ i ∈ List.range 8,CorrectAt 24 (88+i):=by decide +kernel

theorem cr24p12:∀ i ∈ List.range 8,CorrectAt 24 (96+i):=by decide +kernel

theorem cr24p13:∀ i ∈ List.range 8,CorrectAt 24 (104+i):=by decide +kernel

theorem cr24p14:∀ i ∈ List.range 7,CorrectAt 24 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
