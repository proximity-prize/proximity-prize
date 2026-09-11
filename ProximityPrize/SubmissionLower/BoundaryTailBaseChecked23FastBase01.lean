import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastZero08
import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked23FastStrict08

namespace ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
open BoundaryTailBaseChecksData BoundaryTailBaseChecksCore
open BoundaryTailBaseFast BoundaryTailBaseFastData BoundaryTailBaseFastValidated
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async true

theorem br23p0:∀ i ∈ List.range 4,BaseCheckAt 23 (0+i):=by decide +kernel

theorem br23p1:∀ i ∈ List.range 4,BaseCheckAt 23 (4+i):=by decide +kernel

theorem br23p2:∀ i ∈ List.range 4,BaseCheckAt 23 (8+i):=by decide +kernel

theorem br23p3:∀ i ∈ List.range 4,BaseCheckAt 23 (12+i):=by decide +kernel

theorem br23p4:∀ i ∈ List.range 4,BaseCheckAt 23 (16+i):=by decide +kernel

theorem br23p5:∀ i ∈ List.range 4,BaseCheckAt 23 (20+i):=by decide +kernel

theorem br23p6:∀ i ∈ List.range 4,BaseCheckAt 23 (24+i):=by decide +kernel

theorem br23p7:∀ i ∈ List.range 4,BaseCheckAt 23 (28+i):=by decide +kernel

theorem br23p8:∀ i ∈ List.range 4,BaseCheckAt 23 (32+i):=by decide +kernel

theorem br23p9:∀ i ∈ List.range 4,BaseCheckAt 23 (36+i):=by decide +kernel

theorem br23p10:∀ i ∈ List.range 4,BaseCheckAt 23 (40+i):=by decide +kernel

theorem br23p11:∀ i ∈ List.range 4,BaseCheckAt 23 (44+i):=by decide +kernel

theorem br23p12:∀ i ∈ List.range 4,BaseCheckAt 23 (48+i):=by decide +kernel

theorem br23p13:∀ i ∈ List.range 4,BaseCheckAt 23 (52+i):=by decide +kernel

theorem br23p14:∀ i ∈ List.range 4,BaseCheckAt 23 (56+i):=by decide +kernel

theorem br23p15:∀ i ∈ List.range 4,BaseCheckAt 23 (60+i):=by decide +kernel

end ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
