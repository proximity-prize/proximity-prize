import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked10

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr11p0:∀ i ∈ List.range 8,CorrectAt 11 (0+i):=by decide +kernel

theorem cr11p1:∀ i ∈ List.range 8,CorrectAt 11 (8+i):=by decide +kernel

theorem cr11p2:∀ i ∈ List.range 8,CorrectAt 11 (16+i):=by decide +kernel

theorem cr11p3:∀ i ∈ List.range 8,CorrectAt 11 (24+i):=by decide +kernel

theorem cr11p4:∀ i ∈ List.range 8,CorrectAt 11 (32+i):=by decide +kernel

theorem cr11p5:∀ i ∈ List.range 8,CorrectAt 11 (40+i):=by decide +kernel

theorem cr11p6:∀ i ∈ List.range 8,CorrectAt 11 (48+i):=by decide +kernel

theorem cr11p7:∀ i ∈ List.range 8,CorrectAt 11 (56+i):=by decide +kernel

theorem cr11p8:∀ i ∈ List.range 8,CorrectAt 11 (64+i):=by decide +kernel

theorem cr11p9:∀ i ∈ List.range 8,CorrectAt 11 (72+i):=by decide +kernel

theorem cr11p10:∀ i ∈ List.range 8,CorrectAt 11 (80+i):=by decide +kernel

theorem cr11p11:∀ i ∈ List.range 8,CorrectAt 11 (88+i):=by decide +kernel

theorem cr11p12:∀ i ∈ List.range 8,CorrectAt 11 (96+i):=by decide +kernel

theorem cr11p13:∀ i ∈ List.range 8,CorrectAt 11 (104+i):=by decide +kernel

theorem cr11p14:∀ i ∈ List.range 8,CorrectAt 11 (112+i):=by decide +kernel

theorem cr11p15:∀ i ∈ List.range 8,CorrectAt 11 (120+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
