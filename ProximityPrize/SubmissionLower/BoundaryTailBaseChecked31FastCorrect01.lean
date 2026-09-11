import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked30

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr31p0:∀ i ∈ List.range 8,CorrectAt 31 (0+i):=by decide +kernel

theorem cr31p1:∀ i ∈ List.range 8,CorrectAt 31 (8+i):=by decide +kernel

theorem cr31p2:∀ i ∈ List.range 8,CorrectAt 31 (16+i):=by decide +kernel

theorem cr31p3:∀ i ∈ List.range 8,CorrectAt 31 (24+i):=by decide +kernel

theorem cr31p4:∀ i ∈ List.range 8,CorrectAt 31 (32+i):=by decide +kernel

theorem cr31p5:∀ i ∈ List.range 8,CorrectAt 31 (40+i):=by decide +kernel

theorem cr31p6:∀ i ∈ List.range 8,CorrectAt 31 (48+i):=by decide +kernel

theorem cr31p7:∀ i ∈ List.range 8,CorrectAt 31 (56+i):=by decide +kernel

theorem cr31p8:∀ i ∈ List.range 8,CorrectAt 31 (64+i):=by decide +kernel

theorem cr31p9:∀ i ∈ List.range 8,CorrectAt 31 (72+i):=by decide +kernel

theorem cr31p10:∀ i ∈ List.range 8,CorrectAt 31 (80+i):=by decide +kernel

theorem cr31p11:∀ i ∈ List.range 8,CorrectAt 31 (88+i):=by decide +kernel

theorem cr31p12:∀ i ∈ List.range 8,CorrectAt 31 (96+i):=by decide +kernel

theorem cr31p13:∀ i ∈ List.range 8,CorrectAt 31 (104+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
