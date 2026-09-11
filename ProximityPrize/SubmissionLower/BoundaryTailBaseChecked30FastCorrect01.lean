import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked29

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem cr30p0:∀ i ∈ List.range 8,CorrectAt 30 (0+i):=by decide +kernel

theorem cr30p1:∀ i ∈ List.range 8,CorrectAt 30 (8+i):=by decide +kernel

theorem cr30p2:∀ i ∈ List.range 8,CorrectAt 30 (16+i):=by decide +kernel

theorem cr30p3:∀ i ∈ List.range 8,CorrectAt 30 (24+i):=by decide +kernel

theorem cr30p4:∀ i ∈ List.range 8,CorrectAt 30 (32+i):=by decide +kernel

theorem cr30p5:∀ i ∈ List.range 8,CorrectAt 30 (40+i):=by decide +kernel

theorem cr30p6:∀ i ∈ List.range 8,CorrectAt 30 (48+i):=by decide +kernel

theorem cr30p7:∀ i ∈ List.range 8,CorrectAt 30 (56+i):=by decide +kernel

theorem cr30p8:∀ i ∈ List.range 8,CorrectAt 30 (64+i):=by decide +kernel

theorem cr30p9:∀ i ∈ List.range 8,CorrectAt 30 (72+i):=by decide +kernel

theorem cr30p10:∀ i ∈ List.range 8,CorrectAt 30 (80+i):=by decide +kernel

theorem cr30p11:∀ i ∈ List.range 8,CorrectAt 30 (88+i):=by decide +kernel

theorem cr30p12:∀ i ∈ List.range 8,CorrectAt 30 (96+i):=by decide +kernel

theorem cr30p13:∀ i ∈ List.range 8,CorrectAt 30 (104+i):=by decide +kernel

theorem cr30p14:∀ i ∈ List.range 1,CorrectAt 30 (112+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
