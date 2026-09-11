import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked24

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr25p0:∀ i ∈ List.range 8,CorrectAt 25 (0+i):=by decide +kernel

theorem cr25p1:∀ i ∈ List.range 8,CorrectAt 25 (8+i):=by decide +kernel

theorem cr25p2:∀ i ∈ List.range 8,CorrectAt 25 (16+i):=by decide +kernel

theorem cr25p3:∀ i ∈ List.range 8,CorrectAt 25 (24+i):=by decide +kernel

theorem cr25p4:∀ i ∈ List.range 8,CorrectAt 25 (32+i):=by decide +kernel

theorem cr25p5:∀ i ∈ List.range 8,CorrectAt 25 (40+i):=by decide +kernel

theorem cr25p6:∀ i ∈ List.range 8,CorrectAt 25 (48+i):=by decide +kernel

theorem cr25p7:∀ i ∈ List.range 8,CorrectAt 25 (56+i):=by decide +kernel

theorem cr25p8:∀ i ∈ List.range 8,CorrectAt 25 (64+i):=by decide +kernel

theorem cr25p9:∀ i ∈ List.range 8,CorrectAt 25 (72+i):=by decide +kernel

theorem cr25p10:∀ i ∈ List.range 8,CorrectAt 25 (80+i):=by decide +kernel

theorem cr25p11:∀ i ∈ List.range 8,CorrectAt 25 (88+i):=by decide +kernel

theorem cr25p12:∀ i ∈ List.range 8,CorrectAt 25 (96+i):=by decide +kernel

theorem cr25p13:∀ i ∈ List.range 8,CorrectAt 25 (104+i):=by decide +kernel

theorem cr25p14:∀ i ∈ List.range 6,CorrectAt 25 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
