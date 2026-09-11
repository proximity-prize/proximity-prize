import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked03

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr4p0:∀ i ∈ List.range 8,CorrectAt 4 (0+i):=by decide +kernel

theorem cr4p1:∀ i ∈ List.range 8,CorrectAt 4 (8+i):=by decide +kernel

theorem cr4p2:∀ i ∈ List.range 8,CorrectAt 4 (16+i):=by decide +kernel

theorem cr4p3:∀ i ∈ List.range 8,CorrectAt 4 (24+i):=by decide +kernel

theorem cr4p4:∀ i ∈ List.range 8,CorrectAt 4 (32+i):=by decide +kernel

theorem cr4p5:∀ i ∈ List.range 8,CorrectAt 4 (40+i):=by decide +kernel

theorem cr4p6:∀ i ∈ List.range 8,CorrectAt 4 (48+i):=by decide +kernel

theorem cr4p7:∀ i ∈ List.range 8,CorrectAt 4 (56+i):=by decide +kernel

theorem cr4p8:∀ i ∈ List.range 8,CorrectAt 4 (64+i):=by decide +kernel

theorem cr4p9:∀ i ∈ List.range 8,CorrectAt 4 (72+i):=by decide +kernel

theorem cr4p10:∀ i ∈ List.range 8,CorrectAt 4 (80+i):=by decide +kernel

theorem cr4p11:∀ i ∈ List.range 8,CorrectAt 4 (88+i):=by decide +kernel

theorem cr4p12:∀ i ∈ List.range 8,CorrectAt 4 (96+i):=by decide +kernel

theorem cr4p13:∀ i ∈ List.range 8,CorrectAt 4 (104+i):=by decide +kernel

theorem cr4p14:∀ i ∈ List.range 8,CorrectAt 4 (112+i):=by decide +kernel

theorem cr4p15:∀ i ∈ List.range 8,CorrectAt 4 (120+i):=by decide +kernel

theorem cr4p16:∀ i ∈ List.range 8,CorrectAt 4 (128+i):=by decide +kernel

theorem cr4p17:∀ i ∈ List.range 3,CorrectAt 4 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
