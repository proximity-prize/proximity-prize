import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked25

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr26p0:∀ i ∈ List.range 8,CorrectAt 26 (0+i):=by decide +kernel

theorem cr26p1:∀ i ∈ List.range 8,CorrectAt 26 (8+i):=by decide +kernel

theorem cr26p2:∀ i ∈ List.range 8,CorrectAt 26 (16+i):=by decide +kernel

theorem cr26p3:∀ i ∈ List.range 8,CorrectAt 26 (24+i):=by decide +kernel

theorem cr26p4:∀ i ∈ List.range 8,CorrectAt 26 (32+i):=by decide +kernel

theorem cr26p5:∀ i ∈ List.range 8,CorrectAt 26 (40+i):=by decide +kernel

theorem cr26p6:∀ i ∈ List.range 8,CorrectAt 26 (48+i):=by decide +kernel

theorem cr26p7:∀ i ∈ List.range 8,CorrectAt 26 (56+i):=by decide +kernel

theorem cr26p8:∀ i ∈ List.range 8,CorrectAt 26 (64+i):=by decide +kernel

theorem cr26p9:∀ i ∈ List.range 8,CorrectAt 26 (72+i):=by decide +kernel

theorem cr26p10:∀ i ∈ List.range 8,CorrectAt 26 (80+i):=by decide +kernel

theorem cr26p11:∀ i ∈ List.range 8,CorrectAt 26 (88+i):=by decide +kernel

theorem cr26p12:∀ i ∈ List.range 8,CorrectAt 26 (96+i):=by decide +kernel

theorem cr26p13:∀ i ∈ List.range 8,CorrectAt 26 (104+i):=by decide +kernel

theorem cr26p14:∀ i ∈ List.range 5,CorrectAt 26 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
