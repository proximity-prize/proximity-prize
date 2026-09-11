import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked01

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr2p0:∀ i ∈ List.range 8,CorrectAt 2 (0+i):=by decide +kernel

theorem cr2p1:∀ i ∈ List.range 8,CorrectAt 2 (8+i):=by decide +kernel

theorem cr2p2:∀ i ∈ List.range 8,CorrectAt 2 (16+i):=by decide +kernel

theorem cr2p3:∀ i ∈ List.range 8,CorrectAt 2 (24+i):=by decide +kernel

theorem cr2p4:∀ i ∈ List.range 8,CorrectAt 2 (32+i):=by decide +kernel

theorem cr2p5:∀ i ∈ List.range 8,CorrectAt 2 (40+i):=by decide +kernel

theorem cr2p6:∀ i ∈ List.range 8,CorrectAt 2 (48+i):=by decide +kernel

theorem cr2p7:∀ i ∈ List.range 8,CorrectAt 2 (56+i):=by decide +kernel

theorem cr2p8:∀ i ∈ List.range 8,CorrectAt 2 (64+i):=by decide +kernel

theorem cr2p9:∀ i ∈ List.range 8,CorrectAt 2 (72+i):=by decide +kernel

theorem cr2p10:∀ i ∈ List.range 8,CorrectAt 2 (80+i):=by decide +kernel

theorem cr2p11:∀ i ∈ List.range 8,CorrectAt 2 (88+i):=by decide +kernel

theorem cr2p12:∀ i ∈ List.range 8,CorrectAt 2 (96+i):=by decide +kernel

theorem cr2p13:∀ i ∈ List.range 8,CorrectAt 2 (104+i):=by decide +kernel

theorem cr2p14:∀ i ∈ List.range 8,CorrectAt 2 (112+i):=by decide +kernel

theorem cr2p15:∀ i ∈ List.range 8,CorrectAt 2 (120+i):=by decide +kernel

theorem cr2p16:∀ i ∈ List.range 8,CorrectAt 2 (128+i):=by decide +kernel

theorem cr2p17:∀ i ∈ List.range 5,CorrectAt 2 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
