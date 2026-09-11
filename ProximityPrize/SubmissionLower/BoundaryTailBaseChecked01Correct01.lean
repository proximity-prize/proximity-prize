import ProximityPrize.SubmissionLower.BoundaryTailBaseChecksData

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr1p0:∀ i ∈ List.range 8,CorrectAt 1 (0+i):=by decide +kernel

theorem cr1p1:∀ i ∈ List.range 8,CorrectAt 1 (8+i):=by decide +kernel

theorem cr1p2:∀ i ∈ List.range 8,CorrectAt 1 (16+i):=by decide +kernel

theorem cr1p3:∀ i ∈ List.range 8,CorrectAt 1 (24+i):=by decide +kernel

theorem cr1p4:∀ i ∈ List.range 8,CorrectAt 1 (32+i):=by decide +kernel

theorem cr1p5:∀ i ∈ List.range 8,CorrectAt 1 (40+i):=by decide +kernel

theorem cr1p6:∀ i ∈ List.range 8,CorrectAt 1 (48+i):=by decide +kernel

theorem cr1p7:∀ i ∈ List.range 8,CorrectAt 1 (56+i):=by decide +kernel

theorem cr1p8:∀ i ∈ List.range 8,CorrectAt 1 (64+i):=by decide +kernel

theorem cr1p9:∀ i ∈ List.range 8,CorrectAt 1 (72+i):=by decide +kernel

theorem cr1p10:∀ i ∈ List.range 8,CorrectAt 1 (80+i):=by decide +kernel

theorem cr1p11:∀ i ∈ List.range 8,CorrectAt 1 (88+i):=by decide +kernel

theorem cr1p12:∀ i ∈ List.range 8,CorrectAt 1 (96+i):=by decide +kernel

theorem cr1p13:∀ i ∈ List.range 8,CorrectAt 1 (104+i):=by decide +kernel

theorem cr1p14:∀ i ∈ List.range 8,CorrectAt 1 (112+i):=by decide +kernel

theorem cr1p15:∀ i ∈ List.range 8,CorrectAt 1 (120+i):=by decide +kernel

theorem cr1p16:∀ i ∈ List.range 8,CorrectAt 1 (128+i):=by decide +kernel

theorem cr1p17:∀ i ∈ List.range 6,CorrectAt 1 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
