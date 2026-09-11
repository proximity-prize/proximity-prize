import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked04

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr5p0:∀ i ∈ List.range 8,CorrectAt 5 (0+i):=by decide +kernel

theorem cr5p1:∀ i ∈ List.range 8,CorrectAt 5 (8+i):=by decide +kernel

theorem cr5p2:∀ i ∈ List.range 8,CorrectAt 5 (16+i):=by decide +kernel

theorem cr5p3:∀ i ∈ List.range 8,CorrectAt 5 (24+i):=by decide +kernel

theorem cr5p4:∀ i ∈ List.range 8,CorrectAt 5 (32+i):=by decide +kernel

theorem cr5p5:∀ i ∈ List.range 8,CorrectAt 5 (40+i):=by decide +kernel

theorem cr5p6:∀ i ∈ List.range 8,CorrectAt 5 (48+i):=by decide +kernel

theorem cr5p7:∀ i ∈ List.range 8,CorrectAt 5 (56+i):=by decide +kernel

theorem cr5p8:∀ i ∈ List.range 8,CorrectAt 5 (64+i):=by decide +kernel

theorem cr5p9:∀ i ∈ List.range 8,CorrectAt 5 (72+i):=by decide +kernel

theorem cr5p10:∀ i ∈ List.range 8,CorrectAt 5 (80+i):=by decide +kernel

theorem cr5p11:∀ i ∈ List.range 8,CorrectAt 5 (88+i):=by decide +kernel

theorem cr5p12:∀ i ∈ List.range 8,CorrectAt 5 (96+i):=by decide +kernel

theorem cr5p13:∀ i ∈ List.range 8,CorrectAt 5 (104+i):=by decide +kernel

theorem cr5p14:∀ i ∈ List.range 8,CorrectAt 5 (112+i):=by decide +kernel

theorem cr5p15:∀ i ∈ List.range 8,CorrectAt 5 (120+i):=by decide +kernel

theorem cr5p16:∀ i ∈ List.range 8,CorrectAt 5 (128+i):=by decide +kernel

theorem cr5p17:∀ i ∈ List.range 2,CorrectAt 5 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
