import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked27

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr28p0:∀ i ∈ List.range 8,CorrectAt 28 (0+i):=by decide +kernel

theorem cr28p1:∀ i ∈ List.range 8,CorrectAt 28 (8+i):=by decide +kernel

theorem cr28p2:∀ i ∈ List.range 8,CorrectAt 28 (16+i):=by decide +kernel

theorem cr28p3:∀ i ∈ List.range 8,CorrectAt 28 (24+i):=by decide +kernel

theorem cr28p4:∀ i ∈ List.range 8,CorrectAt 28 (32+i):=by decide +kernel

theorem cr28p5:∀ i ∈ List.range 8,CorrectAt 28 (40+i):=by decide +kernel

theorem cr28p6:∀ i ∈ List.range 8,CorrectAt 28 (48+i):=by decide +kernel

theorem cr28p7:∀ i ∈ List.range 8,CorrectAt 28 (56+i):=by decide +kernel

theorem cr28p8:∀ i ∈ List.range 8,CorrectAt 28 (64+i):=by decide +kernel

theorem cr28p9:∀ i ∈ List.range 8,CorrectAt 28 (72+i):=by decide +kernel

theorem cr28p10:∀ i ∈ List.range 8,CorrectAt 28 (80+i):=by decide +kernel

theorem cr28p11:∀ i ∈ List.range 8,CorrectAt 28 (88+i):=by decide +kernel

theorem cr28p12:∀ i ∈ List.range 8,CorrectAt 28 (96+i):=by decide +kernel

theorem cr28p13:∀ i ∈ List.range 8,CorrectAt 28 (104+i):=by decide +kernel

theorem cr28p14:∀ i ∈ List.range 3,CorrectAt 28 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
