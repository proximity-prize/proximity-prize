import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked02

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr3p0:∀ i ∈ List.range 8,CorrectAt 3 (0+i):=by decide +kernel

theorem cr3p1:∀ i ∈ List.range 8,CorrectAt 3 (8+i):=by decide +kernel

theorem cr3p2:∀ i ∈ List.range 8,CorrectAt 3 (16+i):=by decide +kernel

theorem cr3p3:∀ i ∈ List.range 8,CorrectAt 3 (24+i):=by decide +kernel

theorem cr3p4:∀ i ∈ List.range 8,CorrectAt 3 (32+i):=by decide +kernel

theorem cr3p5:∀ i ∈ List.range 8,CorrectAt 3 (40+i):=by decide +kernel

theorem cr3p6:∀ i ∈ List.range 8,CorrectAt 3 (48+i):=by decide +kernel

theorem cr3p7:∀ i ∈ List.range 8,CorrectAt 3 (56+i):=by decide +kernel

theorem cr3p8:∀ i ∈ List.range 8,CorrectAt 3 (64+i):=by decide +kernel

theorem cr3p9:∀ i ∈ List.range 8,CorrectAt 3 (72+i):=by decide +kernel

theorem cr3p10:∀ i ∈ List.range 8,CorrectAt 3 (80+i):=by decide +kernel

theorem cr3p11:∀ i ∈ List.range 8,CorrectAt 3 (88+i):=by decide +kernel

theorem cr3p12:∀ i ∈ List.range 8,CorrectAt 3 (96+i):=by decide +kernel

theorem cr3p13:∀ i ∈ List.range 8,CorrectAt 3 (104+i):=by decide +kernel

theorem cr3p14:∀ i ∈ List.range 8,CorrectAt 3 (112+i):=by decide +kernel

theorem cr3p15:∀ i ∈ List.range 8,CorrectAt 3 (120+i):=by decide +kernel

theorem cr3p16:∀ i ∈ List.range 8,CorrectAt 3 (128+i):=by decide +kernel

theorem cr3p17:∀ i ∈ List.range 4,CorrectAt 3 (136+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
