import ProximityPrize.SubmissionLower.BoundaryTailBaseChecked
import ProximityPrize.SubmissionLower.BoundaryTailPhaseSemantics

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r1_part0 : ∀ i ∈ List.range 8, PrefixAt 1 (0+i) := by decide +kernel

theorem prefix_r1_part8 : ∀ i ∈ List.range 8, PrefixAt 1 (8+i) := by decide +kernel

theorem prefix_r1_part16 : ∀ i ∈ List.range 8, PrefixAt 1 (16+i) := by decide +kernel

theorem prefix_r1_part24 : ∀ i ∈ List.range 8, PrefixAt 1 (24+i) := by decide +kernel

theorem prefix_r1_part32 : ∀ i ∈ List.range 8, PrefixAt 1 (32+i) := by decide +kernel

theorem prefix_r1_part40 : ∀ i ∈ List.range 8, PrefixAt 1 (40+i) := by decide +kernel

theorem prefix_r1_part48 : ∀ i ∈ List.range 8, PrefixAt 1 (48+i) := by decide +kernel

theorem prefix_r1_part56 : ∀ i ∈ List.range 8, PrefixAt 1 (56+i) := by decide +kernel

theorem prefix_r1_part64 : ∀ i ∈ List.range 8, PrefixAt 1 (64+i) := by decide +kernel

theorem prefix_r1_part72 : ∀ i ∈ List.range 8, PrefixAt 1 (72+i) := by decide +kernel

theorem prefix_r1_part80 : ∀ i ∈ List.range 8, PrefixAt 1 (80+i) := by decide +kernel

theorem prefix_r1_part88 : ∀ i ∈ List.range 8, PrefixAt 1 (88+i) := by decide +kernel

theorem prefix_r1_part96 : ∀ i ∈ List.range 8, PrefixAt 1 (96+i) := by decide +kernel

theorem prefix_r1_part104 : ∀ i ∈ List.range 8, PrefixAt 1 (104+i) := by decide +kernel

theorem prefix_r1_part112 : ∀ i ∈ List.range 8, PrefixAt 1 (112+i) := by decide +kernel

theorem prefix_r1_part120 : ∀ i ∈ List.range 8, PrefixAt 1 (120+i) := by decide +kernel

theorem prefix_r1_part128 : ∀ i ∈ List.range 8, PrefixAt 1 (128+i) := by decide +kernel

theorem prefix_r1_part136 : ∀ i ∈ List.range 6, PrefixAt 1 (136+i) := by decide +kernel

theorem prefix_r1 (V : ℕ) (hV : V ∈ List.range 142) : PrefixAt 1 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 1 V)
  have h := (join 0 72 70 (join 0 32 40 (join 0 16 16 (join 0 8 8 prefix_r1_part0 prefix_r1_part8) (join 16 8 8 prefix_r1_part16 prefix_r1_part24)) (join 32 16 24 (join 32 8 8 prefix_r1_part32 prefix_r1_part40) (join 48 8 16 prefix_r1_part48 (join 56 8 8 prefix_r1_part56 prefix_r1_part64)))) (join 72 32 38 (join 72 16 16 (join 72 8 8 prefix_r1_part72 prefix_r1_part80) (join 88 8 8 prefix_r1_part88 prefix_r1_part96)) (join 104 16 22 (join 104 8 8 prefix_r1_part104 prefix_r1_part112) (join 120 8 14 prefix_r1_part120 (join 128 8 6 prefix_r1_part128 prefix_r1_part136)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r2_part0 : ∀ i ∈ List.range 8, PrefixAt 2 (0+i) := by decide +kernel

theorem prefix_r2_part8 : ∀ i ∈ List.range 8, PrefixAt 2 (8+i) := by decide +kernel

theorem prefix_r2_part16 : ∀ i ∈ List.range 8, PrefixAt 2 (16+i) := by decide +kernel

theorem prefix_r2_part24 : ∀ i ∈ List.range 8, PrefixAt 2 (24+i) := by decide +kernel

theorem prefix_r2_part32 : ∀ i ∈ List.range 8, PrefixAt 2 (32+i) := by decide +kernel

theorem prefix_r2_part40 : ∀ i ∈ List.range 8, PrefixAt 2 (40+i) := by decide +kernel

theorem prefix_r2_part48 : ∀ i ∈ List.range 8, PrefixAt 2 (48+i) := by decide +kernel

theorem prefix_r2_part56 : ∀ i ∈ List.range 8, PrefixAt 2 (56+i) := by decide +kernel

theorem prefix_r2_part64 : ∀ i ∈ List.range 8, PrefixAt 2 (64+i) := by decide +kernel

theorem prefix_r2_part72 : ∀ i ∈ List.range 8, PrefixAt 2 (72+i) := by decide +kernel

theorem prefix_r2_part80 : ∀ i ∈ List.range 8, PrefixAt 2 (80+i) := by decide +kernel

theorem prefix_r2_part88 : ∀ i ∈ List.range 8, PrefixAt 2 (88+i) := by decide +kernel

theorem prefix_r2_part96 : ∀ i ∈ List.range 8, PrefixAt 2 (96+i) := by decide +kernel

theorem prefix_r2_part104 : ∀ i ∈ List.range 8, PrefixAt 2 (104+i) := by decide +kernel

theorem prefix_r2_part112 : ∀ i ∈ List.range 8, PrefixAt 2 (112+i) := by decide +kernel

theorem prefix_r2_part120 : ∀ i ∈ List.range 8, PrefixAt 2 (120+i) := by decide +kernel

theorem prefix_r2_part128 : ∀ i ∈ List.range 8, PrefixAt 2 (128+i) := by decide +kernel

theorem prefix_r2_part136 : ∀ i ∈ List.range 5, PrefixAt 2 (136+i) := by decide +kernel

theorem prefix_r2 (V : ℕ) (hV : V ∈ List.range 141) : PrefixAt 2 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 2 V)
  have h := (join 0 72 69 (join 0 32 40 (join 0 16 16 (join 0 8 8 prefix_r2_part0 prefix_r2_part8) (join 16 8 8 prefix_r2_part16 prefix_r2_part24)) (join 32 16 24 (join 32 8 8 prefix_r2_part32 prefix_r2_part40) (join 48 8 16 prefix_r2_part48 (join 56 8 8 prefix_r2_part56 prefix_r2_part64)))) (join 72 32 37 (join 72 16 16 (join 72 8 8 prefix_r2_part72 prefix_r2_part80) (join 88 8 8 prefix_r2_part88 prefix_r2_part96)) (join 104 16 21 (join 104 8 8 prefix_r2_part104 prefix_r2_part112) (join 120 8 13 prefix_r2_part120 (join 128 8 5 prefix_r2_part128 prefix_r2_part136)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r3_part0 : ∀ i ∈ List.range 8, PrefixAt 3 (0+i) := by decide +kernel

theorem prefix_r3_part8 : ∀ i ∈ List.range 8, PrefixAt 3 (8+i) := by decide +kernel

theorem prefix_r3_part16 : ∀ i ∈ List.range 8, PrefixAt 3 (16+i) := by decide +kernel

theorem prefix_r3_part24 : ∀ i ∈ List.range 8, PrefixAt 3 (24+i) := by decide +kernel

theorem prefix_r3_part32 : ∀ i ∈ List.range 8, PrefixAt 3 (32+i) := by decide +kernel

theorem prefix_r3_part40 : ∀ i ∈ List.range 8, PrefixAt 3 (40+i) := by decide +kernel

theorem prefix_r3_part48 : ∀ i ∈ List.range 8, PrefixAt 3 (48+i) := by decide +kernel

theorem prefix_r3_part56 : ∀ i ∈ List.range 8, PrefixAt 3 (56+i) := by decide +kernel

theorem prefix_r3_part64 : ∀ i ∈ List.range 8, PrefixAt 3 (64+i) := by decide +kernel

theorem prefix_r3_part72 : ∀ i ∈ List.range 8, PrefixAt 3 (72+i) := by decide +kernel

theorem prefix_r3_part80 : ∀ i ∈ List.range 8, PrefixAt 3 (80+i) := by decide +kernel

theorem prefix_r3_part88 : ∀ i ∈ List.range 8, PrefixAt 3 (88+i) := by decide +kernel

theorem prefix_r3_part96 : ∀ i ∈ List.range 8, PrefixAt 3 (96+i) := by decide +kernel

theorem prefix_r3_part104 : ∀ i ∈ List.range 8, PrefixAt 3 (104+i) := by decide +kernel

theorem prefix_r3_part112 : ∀ i ∈ List.range 8, PrefixAt 3 (112+i) := by decide +kernel

theorem prefix_r3_part120 : ∀ i ∈ List.range 8, PrefixAt 3 (120+i) := by decide +kernel

theorem prefix_r3_part128 : ∀ i ∈ List.range 8, PrefixAt 3 (128+i) := by decide +kernel

theorem prefix_r3_part136 : ∀ i ∈ List.range 4, PrefixAt 3 (136+i) := by decide +kernel

theorem prefix_r3 (V : ℕ) (hV : V ∈ List.range 140) : PrefixAt 3 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 3 V)
  have h := (join 0 72 68 (join 0 32 40 (join 0 16 16 (join 0 8 8 prefix_r3_part0 prefix_r3_part8) (join 16 8 8 prefix_r3_part16 prefix_r3_part24)) (join 32 16 24 (join 32 8 8 prefix_r3_part32 prefix_r3_part40) (join 48 8 16 prefix_r3_part48 (join 56 8 8 prefix_r3_part56 prefix_r3_part64)))) (join 72 32 36 (join 72 16 16 (join 72 8 8 prefix_r3_part72 prefix_r3_part80) (join 88 8 8 prefix_r3_part88 prefix_r3_part96)) (join 104 16 20 (join 104 8 8 prefix_r3_part104 prefix_r3_part112) (join 120 8 12 prefix_r3_part120 (join 128 8 4 prefix_r3_part128 prefix_r3_part136)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r4_part0 : ∀ i ∈ List.range 8, PrefixAt 4 (0+i) := by decide +kernel

theorem prefix_r4_part8 : ∀ i ∈ List.range 8, PrefixAt 4 (8+i) := by decide +kernel

theorem prefix_r4_part16 : ∀ i ∈ List.range 8, PrefixAt 4 (16+i) := by decide +kernel

theorem prefix_r4_part24 : ∀ i ∈ List.range 8, PrefixAt 4 (24+i) := by decide +kernel

theorem prefix_r4_part32 : ∀ i ∈ List.range 8, PrefixAt 4 (32+i) := by decide +kernel

theorem prefix_r4_part40 : ∀ i ∈ List.range 8, PrefixAt 4 (40+i) := by decide +kernel

theorem prefix_r4_part48 : ∀ i ∈ List.range 8, PrefixAt 4 (48+i) := by decide +kernel

theorem prefix_r4_part56 : ∀ i ∈ List.range 8, PrefixAt 4 (56+i) := by decide +kernel

theorem prefix_r4_part64 : ∀ i ∈ List.range 8, PrefixAt 4 (64+i) := by decide +kernel

theorem prefix_r4_part72 : ∀ i ∈ List.range 8, PrefixAt 4 (72+i) := by decide +kernel

theorem prefix_r4_part80 : ∀ i ∈ List.range 8, PrefixAt 4 (80+i) := by decide +kernel

theorem prefix_r4_part88 : ∀ i ∈ List.range 8, PrefixAt 4 (88+i) := by decide +kernel

theorem prefix_r4_part96 : ∀ i ∈ List.range 8, PrefixAt 4 (96+i) := by decide +kernel

theorem prefix_r4_part104 : ∀ i ∈ List.range 8, PrefixAt 4 (104+i) := by decide +kernel

theorem prefix_r4_part112 : ∀ i ∈ List.range 8, PrefixAt 4 (112+i) := by decide +kernel

theorem prefix_r4_part120 : ∀ i ∈ List.range 8, PrefixAt 4 (120+i) := by decide +kernel

theorem prefix_r4_part128 : ∀ i ∈ List.range 8, PrefixAt 4 (128+i) := by decide +kernel

theorem prefix_r4_part136 : ∀ i ∈ List.range 3, PrefixAt 4 (136+i) := by decide +kernel

theorem prefix_r4 (V : ℕ) (hV : V ∈ List.range 139) : PrefixAt 4 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 4 V)
  have h := (join 0 72 67 (join 0 32 40 (join 0 16 16 (join 0 8 8 prefix_r4_part0 prefix_r4_part8) (join 16 8 8 prefix_r4_part16 prefix_r4_part24)) (join 32 16 24 (join 32 8 8 prefix_r4_part32 prefix_r4_part40) (join 48 8 16 prefix_r4_part48 (join 56 8 8 prefix_r4_part56 prefix_r4_part64)))) (join 72 32 35 (join 72 16 16 (join 72 8 8 prefix_r4_part72 prefix_r4_part80) (join 88 8 8 prefix_r4_part88 prefix_r4_part96)) (join 104 16 19 (join 104 8 8 prefix_r4_part104 prefix_r4_part112) (join 120 8 11 prefix_r4_part120 (join 128 8 3 prefix_r4_part128 prefix_r4_part136)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r5_part0 : ∀ i ∈ List.range 8, PrefixAt 5 (0+i) := by decide +kernel

theorem prefix_r5_part8 : ∀ i ∈ List.range 8, PrefixAt 5 (8+i) := by decide +kernel

theorem prefix_r5_part16 : ∀ i ∈ List.range 8, PrefixAt 5 (16+i) := by decide +kernel

theorem prefix_r5_part24 : ∀ i ∈ List.range 8, PrefixAt 5 (24+i) := by decide +kernel

theorem prefix_r5_part32 : ∀ i ∈ List.range 8, PrefixAt 5 (32+i) := by decide +kernel

theorem prefix_r5_part40 : ∀ i ∈ List.range 8, PrefixAt 5 (40+i) := by decide +kernel

theorem prefix_r5_part48 : ∀ i ∈ List.range 8, PrefixAt 5 (48+i) := by decide +kernel

theorem prefix_r5_part56 : ∀ i ∈ List.range 8, PrefixAt 5 (56+i) := by decide +kernel

theorem prefix_r5_part64 : ∀ i ∈ List.range 8, PrefixAt 5 (64+i) := by decide +kernel

theorem prefix_r5_part72 : ∀ i ∈ List.range 8, PrefixAt 5 (72+i) := by decide +kernel

theorem prefix_r5_part80 : ∀ i ∈ List.range 8, PrefixAt 5 (80+i) := by decide +kernel

theorem prefix_r5_part88 : ∀ i ∈ List.range 8, PrefixAt 5 (88+i) := by decide +kernel

theorem prefix_r5_part96 : ∀ i ∈ List.range 8, PrefixAt 5 (96+i) := by decide +kernel

theorem prefix_r5_part104 : ∀ i ∈ List.range 8, PrefixAt 5 (104+i) := by decide +kernel

theorem prefix_r5_part112 : ∀ i ∈ List.range 8, PrefixAt 5 (112+i) := by decide +kernel

theorem prefix_r5_part120 : ∀ i ∈ List.range 8, PrefixAt 5 (120+i) := by decide +kernel

theorem prefix_r5_part128 : ∀ i ∈ List.range 8, PrefixAt 5 (128+i) := by decide +kernel

theorem prefix_r5_part136 : ∀ i ∈ List.range 2, PrefixAt 5 (136+i) := by decide +kernel

theorem prefix_r5 (V : ℕ) (hV : V ∈ List.range 138) : PrefixAt 5 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 5 V)
  have h := (join 0 72 66 (join 0 32 40 (join 0 16 16 (join 0 8 8 prefix_r5_part0 prefix_r5_part8) (join 16 8 8 prefix_r5_part16 prefix_r5_part24)) (join 32 16 24 (join 32 8 8 prefix_r5_part32 prefix_r5_part40) (join 48 8 16 prefix_r5_part48 (join 56 8 8 prefix_r5_part56 prefix_r5_part64)))) (join 72 32 34 (join 72 16 16 (join 72 8 8 prefix_r5_part72 prefix_r5_part80) (join 88 8 8 prefix_r5_part88 prefix_r5_part96)) (join 104 16 18 (join 104 8 8 prefix_r5_part104 prefix_r5_part112) (join 120 8 10 prefix_r5_part120 (join 128 8 2 prefix_r5_part128 prefix_r5_part136)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r6_part0 : ∀ i ∈ List.range 8, PrefixAt 6 (0+i) := by decide +kernel

theorem prefix_r6_part8 : ∀ i ∈ List.range 8, PrefixAt 6 (8+i) := by decide +kernel

theorem prefix_r6_part16 : ∀ i ∈ List.range 8, PrefixAt 6 (16+i) := by decide +kernel

theorem prefix_r6_part24 : ∀ i ∈ List.range 8, PrefixAt 6 (24+i) := by decide +kernel

theorem prefix_r6_part32 : ∀ i ∈ List.range 8, PrefixAt 6 (32+i) := by decide +kernel

theorem prefix_r6_part40 : ∀ i ∈ List.range 8, PrefixAt 6 (40+i) := by decide +kernel

theorem prefix_r6_part48 : ∀ i ∈ List.range 8, PrefixAt 6 (48+i) := by decide +kernel

theorem prefix_r6_part56 : ∀ i ∈ List.range 8, PrefixAt 6 (56+i) := by decide +kernel

theorem prefix_r6_part64 : ∀ i ∈ List.range 8, PrefixAt 6 (64+i) := by decide +kernel

theorem prefix_r6_part72 : ∀ i ∈ List.range 8, PrefixAt 6 (72+i) := by decide +kernel

theorem prefix_r6_part80 : ∀ i ∈ List.range 8, PrefixAt 6 (80+i) := by decide +kernel

theorem prefix_r6_part88 : ∀ i ∈ List.range 8, PrefixAt 6 (88+i) := by decide +kernel

theorem prefix_r6_part96 : ∀ i ∈ List.range 8, PrefixAt 6 (96+i) := by decide +kernel

theorem prefix_r6_part104 : ∀ i ∈ List.range 8, PrefixAt 6 (104+i) := by decide +kernel

theorem prefix_r6_part112 : ∀ i ∈ List.range 8, PrefixAt 6 (112+i) := by decide +kernel

theorem prefix_r6_part120 : ∀ i ∈ List.range 8, PrefixAt 6 (120+i) := by decide +kernel

theorem prefix_r6_part128 : ∀ i ∈ List.range 8, PrefixAt 6 (128+i) := by decide +kernel

theorem prefix_r6_part136 : ∀ i ∈ List.range 1, PrefixAt 6 (136+i) := by decide +kernel

theorem prefix_r6 (V : ℕ) (hV : V ∈ List.range 137) : PrefixAt 6 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 6 V)
  have h := (join 0 72 65 (join 0 32 40 (join 0 16 16 (join 0 8 8 prefix_r6_part0 prefix_r6_part8) (join 16 8 8 prefix_r6_part16 prefix_r6_part24)) (join 32 16 24 (join 32 8 8 prefix_r6_part32 prefix_r6_part40) (join 48 8 16 prefix_r6_part48 (join 56 8 8 prefix_r6_part56 prefix_r6_part64)))) (join 72 32 33 (join 72 16 16 (join 72 8 8 prefix_r6_part72 prefix_r6_part80) (join 88 8 8 prefix_r6_part88 prefix_r6_part96)) (join 104 16 17 (join 104 8 8 prefix_r6_part104 prefix_r6_part112) (join 120 8 9 prefix_r6_part120 (join 128 8 1 prefix_r6_part128 prefix_r6_part136)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r7_part0 : ∀ i ∈ List.range 8, PrefixAt 7 (0+i) := by decide +kernel

theorem prefix_r7_part8 : ∀ i ∈ List.range 8, PrefixAt 7 (8+i) := by decide +kernel

theorem prefix_r7_part16 : ∀ i ∈ List.range 8, PrefixAt 7 (16+i) := by decide +kernel

theorem prefix_r7_part24 : ∀ i ∈ List.range 8, PrefixAt 7 (24+i) := by decide +kernel

theorem prefix_r7_part32 : ∀ i ∈ List.range 8, PrefixAt 7 (32+i) := by decide +kernel

theorem prefix_r7_part40 : ∀ i ∈ List.range 8, PrefixAt 7 (40+i) := by decide +kernel

theorem prefix_r7_part48 : ∀ i ∈ List.range 8, PrefixAt 7 (48+i) := by decide +kernel

theorem prefix_r7_part56 : ∀ i ∈ List.range 8, PrefixAt 7 (56+i) := by decide +kernel

theorem prefix_r7_part64 : ∀ i ∈ List.range 8, PrefixAt 7 (64+i) := by decide +kernel

theorem prefix_r7_part72 : ∀ i ∈ List.range 8, PrefixAt 7 (72+i) := by decide +kernel

theorem prefix_r7_part80 : ∀ i ∈ List.range 8, PrefixAt 7 (80+i) := by decide +kernel

theorem prefix_r7_part88 : ∀ i ∈ List.range 8, PrefixAt 7 (88+i) := by decide +kernel

theorem prefix_r7_part96 : ∀ i ∈ List.range 8, PrefixAt 7 (96+i) := by decide +kernel

theorem prefix_r7_part104 : ∀ i ∈ List.range 8, PrefixAt 7 (104+i) := by decide +kernel

theorem prefix_r7_part112 : ∀ i ∈ List.range 8, PrefixAt 7 (112+i) := by decide +kernel

theorem prefix_r7_part120 : ∀ i ∈ List.range 8, PrefixAt 7 (120+i) := by decide +kernel

theorem prefix_r7_part128 : ∀ i ∈ List.range 8, PrefixAt 7 (128+i) := by decide +kernel

theorem prefix_r7 (V : ℕ) (hV : V ∈ List.range 136) : PrefixAt 7 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 7 V)
  have h := (join 0 64 72 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r7_part0 prefix_r7_part8) (join 16 8 8 prefix_r7_part16 prefix_r7_part24)) (join 32 16 16 (join 32 8 8 prefix_r7_part32 prefix_r7_part40) (join 48 8 8 prefix_r7_part48 prefix_r7_part56))) (join 64 32 40 (join 64 16 16 (join 64 8 8 prefix_r7_part64 prefix_r7_part72) (join 80 8 8 prefix_r7_part80 prefix_r7_part88)) (join 96 16 24 (join 96 8 8 prefix_r7_part96 prefix_r7_part104) (join 112 8 16 prefix_r7_part112 (join 120 8 8 prefix_r7_part120 prefix_r7_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r8_part0 : ∀ i ∈ List.range 8, PrefixAt 8 (0+i) := by decide +kernel

theorem prefix_r8_part8 : ∀ i ∈ List.range 8, PrefixAt 8 (8+i) := by decide +kernel

theorem prefix_r8_part16 : ∀ i ∈ List.range 8, PrefixAt 8 (16+i) := by decide +kernel

theorem prefix_r8_part24 : ∀ i ∈ List.range 8, PrefixAt 8 (24+i) := by decide +kernel

theorem prefix_r8_part32 : ∀ i ∈ List.range 8, PrefixAt 8 (32+i) := by decide +kernel

theorem prefix_r8_part40 : ∀ i ∈ List.range 8, PrefixAt 8 (40+i) := by decide +kernel

theorem prefix_r8_part48 : ∀ i ∈ List.range 8, PrefixAt 8 (48+i) := by decide +kernel

theorem prefix_r8_part56 : ∀ i ∈ List.range 8, PrefixAt 8 (56+i) := by decide +kernel

theorem prefix_r8_part64 : ∀ i ∈ List.range 8, PrefixAt 8 (64+i) := by decide +kernel

theorem prefix_r8_part72 : ∀ i ∈ List.range 8, PrefixAt 8 (72+i) := by decide +kernel

theorem prefix_r8_part80 : ∀ i ∈ List.range 8, PrefixAt 8 (80+i) := by decide +kernel

theorem prefix_r8_part88 : ∀ i ∈ List.range 8, PrefixAt 8 (88+i) := by decide +kernel

theorem prefix_r8_part96 : ∀ i ∈ List.range 8, PrefixAt 8 (96+i) := by decide +kernel

theorem prefix_r8_part104 : ∀ i ∈ List.range 8, PrefixAt 8 (104+i) := by decide +kernel

theorem prefix_r8_part112 : ∀ i ∈ List.range 8, PrefixAt 8 (112+i) := by decide +kernel

theorem prefix_r8_part120 : ∀ i ∈ List.range 8, PrefixAt 8 (120+i) := by decide +kernel

theorem prefix_r8_part128 : ∀ i ∈ List.range 7, PrefixAt 8 (128+i) := by decide +kernel

theorem prefix_r8 (V : ℕ) (hV : V ∈ List.range 135) : PrefixAt 8 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 8 V)
  have h := (join 0 64 71 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r8_part0 prefix_r8_part8) (join 16 8 8 prefix_r8_part16 prefix_r8_part24)) (join 32 16 16 (join 32 8 8 prefix_r8_part32 prefix_r8_part40) (join 48 8 8 prefix_r8_part48 prefix_r8_part56))) (join 64 32 39 (join 64 16 16 (join 64 8 8 prefix_r8_part64 prefix_r8_part72) (join 80 8 8 prefix_r8_part80 prefix_r8_part88)) (join 96 16 23 (join 96 8 8 prefix_r8_part96 prefix_r8_part104) (join 112 8 15 prefix_r8_part112 (join 120 8 7 prefix_r8_part120 prefix_r8_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r9_part0 : ∀ i ∈ List.range 8, PrefixAt 9 (0+i) := by decide +kernel

theorem prefix_r9_part8 : ∀ i ∈ List.range 8, PrefixAt 9 (8+i) := by decide +kernel

theorem prefix_r9_part16 : ∀ i ∈ List.range 8, PrefixAt 9 (16+i) := by decide +kernel

theorem prefix_r9_part24 : ∀ i ∈ List.range 8, PrefixAt 9 (24+i) := by decide +kernel

theorem prefix_r9_part32 : ∀ i ∈ List.range 8, PrefixAt 9 (32+i) := by decide +kernel

theorem prefix_r9_part40 : ∀ i ∈ List.range 8, PrefixAt 9 (40+i) := by decide +kernel

theorem prefix_r9_part48 : ∀ i ∈ List.range 8, PrefixAt 9 (48+i) := by decide +kernel

theorem prefix_r9_part56 : ∀ i ∈ List.range 8, PrefixAt 9 (56+i) := by decide +kernel

theorem prefix_r9_part64 : ∀ i ∈ List.range 8, PrefixAt 9 (64+i) := by decide +kernel

theorem prefix_r9_part72 : ∀ i ∈ List.range 8, PrefixAt 9 (72+i) := by decide +kernel

theorem prefix_r9_part80 : ∀ i ∈ List.range 8, PrefixAt 9 (80+i) := by decide +kernel

theorem prefix_r9_part88 : ∀ i ∈ List.range 8, PrefixAt 9 (88+i) := by decide +kernel

theorem prefix_r9_part96 : ∀ i ∈ List.range 8, PrefixAt 9 (96+i) := by decide +kernel

theorem prefix_r9_part104 : ∀ i ∈ List.range 8, PrefixAt 9 (104+i) := by decide +kernel

theorem prefix_r9_part112 : ∀ i ∈ List.range 8, PrefixAt 9 (112+i) := by decide +kernel

theorem prefix_r9_part120 : ∀ i ∈ List.range 8, PrefixAt 9 (120+i) := by decide +kernel

theorem prefix_r9_part128 : ∀ i ∈ List.range 6, PrefixAt 9 (128+i) := by decide +kernel

theorem prefix_r9 (V : ℕ) (hV : V ∈ List.range 134) : PrefixAt 9 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 9 V)
  have h := (join 0 64 70 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r9_part0 prefix_r9_part8) (join 16 8 8 prefix_r9_part16 prefix_r9_part24)) (join 32 16 16 (join 32 8 8 prefix_r9_part32 prefix_r9_part40) (join 48 8 8 prefix_r9_part48 prefix_r9_part56))) (join 64 32 38 (join 64 16 16 (join 64 8 8 prefix_r9_part64 prefix_r9_part72) (join 80 8 8 prefix_r9_part80 prefix_r9_part88)) (join 96 16 22 (join 96 8 8 prefix_r9_part96 prefix_r9_part104) (join 112 8 14 prefix_r9_part112 (join 120 8 6 prefix_r9_part120 prefix_r9_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r10_part0 : ∀ i ∈ List.range 8, PrefixAt 10 (0+i) := by decide +kernel

theorem prefix_r10_part8 : ∀ i ∈ List.range 8, PrefixAt 10 (8+i) := by decide +kernel

theorem prefix_r10_part16 : ∀ i ∈ List.range 8, PrefixAt 10 (16+i) := by decide +kernel

theorem prefix_r10_part24 : ∀ i ∈ List.range 8, PrefixAt 10 (24+i) := by decide +kernel

theorem prefix_r10_part32 : ∀ i ∈ List.range 8, PrefixAt 10 (32+i) := by decide +kernel

theorem prefix_r10_part40 : ∀ i ∈ List.range 8, PrefixAt 10 (40+i) := by decide +kernel

theorem prefix_r10_part48 : ∀ i ∈ List.range 8, PrefixAt 10 (48+i) := by decide +kernel

theorem prefix_r10_part56 : ∀ i ∈ List.range 8, PrefixAt 10 (56+i) := by decide +kernel

theorem prefix_r10_part64 : ∀ i ∈ List.range 8, PrefixAt 10 (64+i) := by decide +kernel

theorem prefix_r10_part72 : ∀ i ∈ List.range 8, PrefixAt 10 (72+i) := by decide +kernel

theorem prefix_r10_part80 : ∀ i ∈ List.range 8, PrefixAt 10 (80+i) := by decide +kernel

theorem prefix_r10_part88 : ∀ i ∈ List.range 8, PrefixAt 10 (88+i) := by decide +kernel

theorem prefix_r10_part96 : ∀ i ∈ List.range 8, PrefixAt 10 (96+i) := by decide +kernel

theorem prefix_r10_part104 : ∀ i ∈ List.range 8, PrefixAt 10 (104+i) := by decide +kernel

theorem prefix_r10_part112 : ∀ i ∈ List.range 8, PrefixAt 10 (112+i) := by decide +kernel

theorem prefix_r10_part120 : ∀ i ∈ List.range 8, PrefixAt 10 (120+i) := by decide +kernel

theorem prefix_r10_part128 : ∀ i ∈ List.range 5, PrefixAt 10 (128+i) := by decide +kernel

theorem prefix_r10 (V : ℕ) (hV : V ∈ List.range 133) : PrefixAt 10 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 10 V)
  have h := (join 0 64 69 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r10_part0 prefix_r10_part8) (join 16 8 8 prefix_r10_part16 prefix_r10_part24)) (join 32 16 16 (join 32 8 8 prefix_r10_part32 prefix_r10_part40) (join 48 8 8 prefix_r10_part48 prefix_r10_part56))) (join 64 32 37 (join 64 16 16 (join 64 8 8 prefix_r10_part64 prefix_r10_part72) (join 80 8 8 prefix_r10_part80 prefix_r10_part88)) (join 96 16 21 (join 96 8 8 prefix_r10_part96 prefix_r10_part104) (join 112 8 13 prefix_r10_part112 (join 120 8 5 prefix_r10_part120 prefix_r10_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r11_part0 : ∀ i ∈ List.range 8, PrefixAt 11 (0+i) := by decide +kernel

theorem prefix_r11_part8 : ∀ i ∈ List.range 8, PrefixAt 11 (8+i) := by decide +kernel

theorem prefix_r11_part16 : ∀ i ∈ List.range 8, PrefixAt 11 (16+i) := by decide +kernel

theorem prefix_r11_part24 : ∀ i ∈ List.range 8, PrefixAt 11 (24+i) := by decide +kernel

theorem prefix_r11_part32 : ∀ i ∈ List.range 8, PrefixAt 11 (32+i) := by decide +kernel

theorem prefix_r11_part40 : ∀ i ∈ List.range 8, PrefixAt 11 (40+i) := by decide +kernel

theorem prefix_r11_part48 : ∀ i ∈ List.range 8, PrefixAt 11 (48+i) := by decide +kernel

theorem prefix_r11_part56 : ∀ i ∈ List.range 8, PrefixAt 11 (56+i) := by decide +kernel

theorem prefix_r11_part64 : ∀ i ∈ List.range 8, PrefixAt 11 (64+i) := by decide +kernel

theorem prefix_r11_part72 : ∀ i ∈ List.range 8, PrefixAt 11 (72+i) := by decide +kernel

theorem prefix_r11_part80 : ∀ i ∈ List.range 8, PrefixAt 11 (80+i) := by decide +kernel

theorem prefix_r11_part88 : ∀ i ∈ List.range 8, PrefixAt 11 (88+i) := by decide +kernel

theorem prefix_r11_part96 : ∀ i ∈ List.range 8, PrefixAt 11 (96+i) := by decide +kernel

theorem prefix_r11_part104 : ∀ i ∈ List.range 8, PrefixAt 11 (104+i) := by decide +kernel

theorem prefix_r11_part112 : ∀ i ∈ List.range 8, PrefixAt 11 (112+i) := by decide +kernel

theorem prefix_r11_part120 : ∀ i ∈ List.range 8, PrefixAt 11 (120+i) := by decide +kernel

theorem prefix_r11_part128 : ∀ i ∈ List.range 4, PrefixAt 11 (128+i) := by decide +kernel

theorem prefix_r11 (V : ℕ) (hV : V ∈ List.range 132) : PrefixAt 11 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 11 V)
  have h := (join 0 64 68 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r11_part0 prefix_r11_part8) (join 16 8 8 prefix_r11_part16 prefix_r11_part24)) (join 32 16 16 (join 32 8 8 prefix_r11_part32 prefix_r11_part40) (join 48 8 8 prefix_r11_part48 prefix_r11_part56))) (join 64 32 36 (join 64 16 16 (join 64 8 8 prefix_r11_part64 prefix_r11_part72) (join 80 8 8 prefix_r11_part80 prefix_r11_part88)) (join 96 16 20 (join 96 8 8 prefix_r11_part96 prefix_r11_part104) (join 112 8 12 prefix_r11_part112 (join 120 8 4 prefix_r11_part120 prefix_r11_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r12_part0 : ∀ i ∈ List.range 8, PrefixAt 12 (0+i) := by decide +kernel

theorem prefix_r12_part8 : ∀ i ∈ List.range 8, PrefixAt 12 (8+i) := by decide +kernel

theorem prefix_r12_part16 : ∀ i ∈ List.range 8, PrefixAt 12 (16+i) := by decide +kernel

theorem prefix_r12_part24 : ∀ i ∈ List.range 8, PrefixAt 12 (24+i) := by decide +kernel

theorem prefix_r12_part32 : ∀ i ∈ List.range 8, PrefixAt 12 (32+i) := by decide +kernel

theorem prefix_r12_part40 : ∀ i ∈ List.range 8, PrefixAt 12 (40+i) := by decide +kernel

theorem prefix_r12_part48 : ∀ i ∈ List.range 8, PrefixAt 12 (48+i) := by decide +kernel

theorem prefix_r12_part56 : ∀ i ∈ List.range 8, PrefixAt 12 (56+i) := by decide +kernel

theorem prefix_r12_part64 : ∀ i ∈ List.range 8, PrefixAt 12 (64+i) := by decide +kernel

theorem prefix_r12_part72 : ∀ i ∈ List.range 8, PrefixAt 12 (72+i) := by decide +kernel

theorem prefix_r12_part80 : ∀ i ∈ List.range 8, PrefixAt 12 (80+i) := by decide +kernel

theorem prefix_r12_part88 : ∀ i ∈ List.range 8, PrefixAt 12 (88+i) := by decide +kernel

theorem prefix_r12_part96 : ∀ i ∈ List.range 8, PrefixAt 12 (96+i) := by decide +kernel

theorem prefix_r12_part104 : ∀ i ∈ List.range 8, PrefixAt 12 (104+i) := by decide +kernel

theorem prefix_r12_part112 : ∀ i ∈ List.range 8, PrefixAt 12 (112+i) := by decide +kernel

theorem prefix_r12_part120 : ∀ i ∈ List.range 8, PrefixAt 12 (120+i) := by decide +kernel

theorem prefix_r12_part128 : ∀ i ∈ List.range 3, PrefixAt 12 (128+i) := by decide +kernel

theorem prefix_r12 (V : ℕ) (hV : V ∈ List.range 131) : PrefixAt 12 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 12 V)
  have h := (join 0 64 67 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r12_part0 prefix_r12_part8) (join 16 8 8 prefix_r12_part16 prefix_r12_part24)) (join 32 16 16 (join 32 8 8 prefix_r12_part32 prefix_r12_part40) (join 48 8 8 prefix_r12_part48 prefix_r12_part56))) (join 64 32 35 (join 64 16 16 (join 64 8 8 prefix_r12_part64 prefix_r12_part72) (join 80 8 8 prefix_r12_part80 prefix_r12_part88)) (join 96 16 19 (join 96 8 8 prefix_r12_part96 prefix_r12_part104) (join 112 8 11 prefix_r12_part112 (join 120 8 3 prefix_r12_part120 prefix_r12_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r13_part0 : ∀ i ∈ List.range 8, PrefixAt 13 (0+i) := by decide +kernel

theorem prefix_r13_part8 : ∀ i ∈ List.range 8, PrefixAt 13 (8+i) := by decide +kernel

theorem prefix_r13_part16 : ∀ i ∈ List.range 8, PrefixAt 13 (16+i) := by decide +kernel

theorem prefix_r13_part24 : ∀ i ∈ List.range 8, PrefixAt 13 (24+i) := by decide +kernel

theorem prefix_r13_part32 : ∀ i ∈ List.range 8, PrefixAt 13 (32+i) := by decide +kernel

theorem prefix_r13_part40 : ∀ i ∈ List.range 8, PrefixAt 13 (40+i) := by decide +kernel

theorem prefix_r13_part48 : ∀ i ∈ List.range 8, PrefixAt 13 (48+i) := by decide +kernel

theorem prefix_r13_part56 : ∀ i ∈ List.range 8, PrefixAt 13 (56+i) := by decide +kernel

theorem prefix_r13_part64 : ∀ i ∈ List.range 8, PrefixAt 13 (64+i) := by decide +kernel

theorem prefix_r13_part72 : ∀ i ∈ List.range 8, PrefixAt 13 (72+i) := by decide +kernel

theorem prefix_r13_part80 : ∀ i ∈ List.range 8, PrefixAt 13 (80+i) := by decide +kernel

theorem prefix_r13_part88 : ∀ i ∈ List.range 8, PrefixAt 13 (88+i) := by decide +kernel

theorem prefix_r13_part96 : ∀ i ∈ List.range 8, PrefixAt 13 (96+i) := by decide +kernel

theorem prefix_r13_part104 : ∀ i ∈ List.range 8, PrefixAt 13 (104+i) := by decide +kernel

theorem prefix_r13_part112 : ∀ i ∈ List.range 8, PrefixAt 13 (112+i) := by decide +kernel

theorem prefix_r13_part120 : ∀ i ∈ List.range 8, PrefixAt 13 (120+i) := by decide +kernel

theorem prefix_r13_part128 : ∀ i ∈ List.range 2, PrefixAt 13 (128+i) := by decide +kernel

theorem prefix_r13 (V : ℕ) (hV : V ∈ List.range 130) : PrefixAt 13 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 13 V)
  have h := (join 0 64 66 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r13_part0 prefix_r13_part8) (join 16 8 8 prefix_r13_part16 prefix_r13_part24)) (join 32 16 16 (join 32 8 8 prefix_r13_part32 prefix_r13_part40) (join 48 8 8 prefix_r13_part48 prefix_r13_part56))) (join 64 32 34 (join 64 16 16 (join 64 8 8 prefix_r13_part64 prefix_r13_part72) (join 80 8 8 prefix_r13_part80 prefix_r13_part88)) (join 96 16 18 (join 96 8 8 prefix_r13_part96 prefix_r13_part104) (join 112 8 10 prefix_r13_part112 (join 120 8 2 prefix_r13_part120 prefix_r13_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r14_part0 : ∀ i ∈ List.range 8, PrefixAt 14 (0+i) := by decide +kernel

theorem prefix_r14_part8 : ∀ i ∈ List.range 8, PrefixAt 14 (8+i) := by decide +kernel

theorem prefix_r14_part16 : ∀ i ∈ List.range 8, PrefixAt 14 (16+i) := by decide +kernel

theorem prefix_r14_part24 : ∀ i ∈ List.range 8, PrefixAt 14 (24+i) := by decide +kernel

theorem prefix_r14_part32 : ∀ i ∈ List.range 8, PrefixAt 14 (32+i) := by decide +kernel

theorem prefix_r14_part40 : ∀ i ∈ List.range 8, PrefixAt 14 (40+i) := by decide +kernel

theorem prefix_r14_part48 : ∀ i ∈ List.range 8, PrefixAt 14 (48+i) := by decide +kernel

theorem prefix_r14_part56 : ∀ i ∈ List.range 8, PrefixAt 14 (56+i) := by decide +kernel

theorem prefix_r14_part64 : ∀ i ∈ List.range 8, PrefixAt 14 (64+i) := by decide +kernel

theorem prefix_r14_part72 : ∀ i ∈ List.range 8, PrefixAt 14 (72+i) := by decide +kernel

theorem prefix_r14_part80 : ∀ i ∈ List.range 8, PrefixAt 14 (80+i) := by decide +kernel

theorem prefix_r14_part88 : ∀ i ∈ List.range 8, PrefixAt 14 (88+i) := by decide +kernel

theorem prefix_r14_part96 : ∀ i ∈ List.range 8, PrefixAt 14 (96+i) := by decide +kernel

theorem prefix_r14_part104 : ∀ i ∈ List.range 8, PrefixAt 14 (104+i) := by decide +kernel

theorem prefix_r14_part112 : ∀ i ∈ List.range 8, PrefixAt 14 (112+i) := by decide +kernel

theorem prefix_r14_part120 : ∀ i ∈ List.range 8, PrefixAt 14 (120+i) := by decide +kernel

theorem prefix_r14_part128 : ∀ i ∈ List.range 1, PrefixAt 14 (128+i) := by decide +kernel

theorem prefix_r14 (V : ℕ) (hV : V ∈ List.range 129) : PrefixAt 14 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 14 V)
  have h := (join 0 64 65 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r14_part0 prefix_r14_part8) (join 16 8 8 prefix_r14_part16 prefix_r14_part24)) (join 32 16 16 (join 32 8 8 prefix_r14_part32 prefix_r14_part40) (join 48 8 8 prefix_r14_part48 prefix_r14_part56))) (join 64 32 33 (join 64 16 16 (join 64 8 8 prefix_r14_part64 prefix_r14_part72) (join 80 8 8 prefix_r14_part80 prefix_r14_part88)) (join 96 16 17 (join 96 8 8 prefix_r14_part96 prefix_r14_part104) (join 112 8 9 prefix_r14_part112 (join 120 8 1 prefix_r14_part120 prefix_r14_part128)))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r15_part0 : ∀ i ∈ List.range 8, PrefixAt 15 (0+i) := by decide +kernel

theorem prefix_r15_part8 : ∀ i ∈ List.range 8, PrefixAt 15 (8+i) := by decide +kernel

theorem prefix_r15_part16 : ∀ i ∈ List.range 8, PrefixAt 15 (16+i) := by decide +kernel

theorem prefix_r15_part24 : ∀ i ∈ List.range 8, PrefixAt 15 (24+i) := by decide +kernel

theorem prefix_r15_part32 : ∀ i ∈ List.range 8, PrefixAt 15 (32+i) := by decide +kernel

theorem prefix_r15_part40 : ∀ i ∈ List.range 8, PrefixAt 15 (40+i) := by decide +kernel

theorem prefix_r15_part48 : ∀ i ∈ List.range 8, PrefixAt 15 (48+i) := by decide +kernel

theorem prefix_r15_part56 : ∀ i ∈ List.range 8, PrefixAt 15 (56+i) := by decide +kernel

theorem prefix_r15_part64 : ∀ i ∈ List.range 8, PrefixAt 15 (64+i) := by decide +kernel

theorem prefix_r15_part72 : ∀ i ∈ List.range 8, PrefixAt 15 (72+i) := by decide +kernel

theorem prefix_r15_part80 : ∀ i ∈ List.range 8, PrefixAt 15 (80+i) := by decide +kernel

theorem prefix_r15_part88 : ∀ i ∈ List.range 8, PrefixAt 15 (88+i) := by decide +kernel

theorem prefix_r15_part96 : ∀ i ∈ List.range 8, PrefixAt 15 (96+i) := by decide +kernel

theorem prefix_r15_part104 : ∀ i ∈ List.range 8, PrefixAt 15 (104+i) := by decide +kernel

theorem prefix_r15_part112 : ∀ i ∈ List.range 8, PrefixAt 15 (112+i) := by decide +kernel

theorem prefix_r15_part120 : ∀ i ∈ List.range 8, PrefixAt 15 (120+i) := by decide +kernel

theorem prefix_r15 (V : ℕ) (hV : V ∈ List.range 128) : PrefixAt 15 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 15 V)
  have h := (join 0 64 64 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r15_part0 prefix_r15_part8) (join 16 8 8 prefix_r15_part16 prefix_r15_part24)) (join 32 16 16 (join 32 8 8 prefix_r15_part32 prefix_r15_part40) (join 48 8 8 prefix_r15_part48 prefix_r15_part56))) (join 64 32 32 (join 64 16 16 (join 64 8 8 prefix_r15_part64 prefix_r15_part72) (join 80 8 8 prefix_r15_part80 prefix_r15_part88)) (join 96 16 16 (join 96 8 8 prefix_r15_part96 prefix_r15_part104) (join 112 8 8 prefix_r15_part112 prefix_r15_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r16_part0 : ∀ i ∈ List.range 8, PrefixAt 16 (0+i) := by decide +kernel

theorem prefix_r16_part8 : ∀ i ∈ List.range 8, PrefixAt 16 (8+i) := by decide +kernel

theorem prefix_r16_part16 : ∀ i ∈ List.range 8, PrefixAt 16 (16+i) := by decide +kernel

theorem prefix_r16_part24 : ∀ i ∈ List.range 8, PrefixAt 16 (24+i) := by decide +kernel

theorem prefix_r16_part32 : ∀ i ∈ List.range 8, PrefixAt 16 (32+i) := by decide +kernel

theorem prefix_r16_part40 : ∀ i ∈ List.range 8, PrefixAt 16 (40+i) := by decide +kernel

theorem prefix_r16_part48 : ∀ i ∈ List.range 8, PrefixAt 16 (48+i) := by decide +kernel

theorem prefix_r16_part56 : ∀ i ∈ List.range 8, PrefixAt 16 (56+i) := by decide +kernel

theorem prefix_r16_part64 : ∀ i ∈ List.range 8, PrefixAt 16 (64+i) := by decide +kernel

theorem prefix_r16_part72 : ∀ i ∈ List.range 8, PrefixAt 16 (72+i) := by decide +kernel

theorem prefix_r16_part80 : ∀ i ∈ List.range 8, PrefixAt 16 (80+i) := by decide +kernel

theorem prefix_r16_part88 : ∀ i ∈ List.range 8, PrefixAt 16 (88+i) := by decide +kernel

theorem prefix_r16_part96 : ∀ i ∈ List.range 8, PrefixAt 16 (96+i) := by decide +kernel

theorem prefix_r16_part104 : ∀ i ∈ List.range 8, PrefixAt 16 (104+i) := by decide +kernel

theorem prefix_r16_part112 : ∀ i ∈ List.range 8, PrefixAt 16 (112+i) := by decide +kernel

theorem prefix_r16_part120 : ∀ i ∈ List.range 7, PrefixAt 16 (120+i) := by decide +kernel

theorem prefix_r16 (V : ℕ) (hV : V ∈ List.range 127) : PrefixAt 16 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 16 V)
  have h := (join 0 64 63 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r16_part0 prefix_r16_part8) (join 16 8 8 prefix_r16_part16 prefix_r16_part24)) (join 32 16 16 (join 32 8 8 prefix_r16_part32 prefix_r16_part40) (join 48 8 8 prefix_r16_part48 prefix_r16_part56))) (join 64 32 31 (join 64 16 16 (join 64 8 8 prefix_r16_part64 prefix_r16_part72) (join 80 8 8 prefix_r16_part80 prefix_r16_part88)) (join 96 16 15 (join 96 8 8 prefix_r16_part96 prefix_r16_part104) (join 112 8 7 prefix_r16_part112 prefix_r16_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r17_part0 : ∀ i ∈ List.range 8, PrefixAt 17 (0+i) := by decide +kernel

theorem prefix_r17_part8 : ∀ i ∈ List.range 8, PrefixAt 17 (8+i) := by decide +kernel

theorem prefix_r17_part16 : ∀ i ∈ List.range 8, PrefixAt 17 (16+i) := by decide +kernel

theorem prefix_r17_part24 : ∀ i ∈ List.range 8, PrefixAt 17 (24+i) := by decide +kernel

theorem prefix_r17_part32 : ∀ i ∈ List.range 8, PrefixAt 17 (32+i) := by decide +kernel

theorem prefix_r17_part40 : ∀ i ∈ List.range 8, PrefixAt 17 (40+i) := by decide +kernel

theorem prefix_r17_part48 : ∀ i ∈ List.range 8, PrefixAt 17 (48+i) := by decide +kernel

theorem prefix_r17_part56 : ∀ i ∈ List.range 8, PrefixAt 17 (56+i) := by decide +kernel

theorem prefix_r17_part64 : ∀ i ∈ List.range 8, PrefixAt 17 (64+i) := by decide +kernel

theorem prefix_r17_part72 : ∀ i ∈ List.range 8, PrefixAt 17 (72+i) := by decide +kernel

theorem prefix_r17_part80 : ∀ i ∈ List.range 8, PrefixAt 17 (80+i) := by decide +kernel

theorem prefix_r17_part88 : ∀ i ∈ List.range 8, PrefixAt 17 (88+i) := by decide +kernel

theorem prefix_r17_part96 : ∀ i ∈ List.range 8, PrefixAt 17 (96+i) := by decide +kernel

theorem prefix_r17_part104 : ∀ i ∈ List.range 8, PrefixAt 17 (104+i) := by decide +kernel

theorem prefix_r17_part112 : ∀ i ∈ List.range 8, PrefixAt 17 (112+i) := by decide +kernel

theorem prefix_r17_part120 : ∀ i ∈ List.range 6, PrefixAt 17 (120+i) := by decide +kernel

theorem prefix_r17 (V : ℕ) (hV : V ∈ List.range 126) : PrefixAt 17 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 17 V)
  have h := (join 0 64 62 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r17_part0 prefix_r17_part8) (join 16 8 8 prefix_r17_part16 prefix_r17_part24)) (join 32 16 16 (join 32 8 8 prefix_r17_part32 prefix_r17_part40) (join 48 8 8 prefix_r17_part48 prefix_r17_part56))) (join 64 32 30 (join 64 16 16 (join 64 8 8 prefix_r17_part64 prefix_r17_part72) (join 80 8 8 prefix_r17_part80 prefix_r17_part88)) (join 96 16 14 (join 96 8 8 prefix_r17_part96 prefix_r17_part104) (join 112 8 6 prefix_r17_part112 prefix_r17_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r18_part0 : ∀ i ∈ List.range 8, PrefixAt 18 (0+i) := by decide +kernel

theorem prefix_r18_part8 : ∀ i ∈ List.range 8, PrefixAt 18 (8+i) := by decide +kernel

theorem prefix_r18_part16 : ∀ i ∈ List.range 8, PrefixAt 18 (16+i) := by decide +kernel

theorem prefix_r18_part24 : ∀ i ∈ List.range 8, PrefixAt 18 (24+i) := by decide +kernel

theorem prefix_r18_part32 : ∀ i ∈ List.range 8, PrefixAt 18 (32+i) := by decide +kernel

theorem prefix_r18_part40 : ∀ i ∈ List.range 8, PrefixAt 18 (40+i) := by decide +kernel

theorem prefix_r18_part48 : ∀ i ∈ List.range 8, PrefixAt 18 (48+i) := by decide +kernel

theorem prefix_r18_part56 : ∀ i ∈ List.range 8, PrefixAt 18 (56+i) := by decide +kernel

theorem prefix_r18_part64 : ∀ i ∈ List.range 8, PrefixAt 18 (64+i) := by decide +kernel

theorem prefix_r18_part72 : ∀ i ∈ List.range 8, PrefixAt 18 (72+i) := by decide +kernel

theorem prefix_r18_part80 : ∀ i ∈ List.range 8, PrefixAt 18 (80+i) := by decide +kernel

theorem prefix_r18_part88 : ∀ i ∈ List.range 8, PrefixAt 18 (88+i) := by decide +kernel

theorem prefix_r18_part96 : ∀ i ∈ List.range 8, PrefixAt 18 (96+i) := by decide +kernel

theorem prefix_r18_part104 : ∀ i ∈ List.range 8, PrefixAt 18 (104+i) := by decide +kernel

theorem prefix_r18_part112 : ∀ i ∈ List.range 8, PrefixAt 18 (112+i) := by decide +kernel

theorem prefix_r18_part120 : ∀ i ∈ List.range 5, PrefixAt 18 (120+i) := by decide +kernel

theorem prefix_r18 (V : ℕ) (hV : V ∈ List.range 125) : PrefixAt 18 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 18 V)
  have h := (join 0 64 61 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r18_part0 prefix_r18_part8) (join 16 8 8 prefix_r18_part16 prefix_r18_part24)) (join 32 16 16 (join 32 8 8 prefix_r18_part32 prefix_r18_part40) (join 48 8 8 prefix_r18_part48 prefix_r18_part56))) (join 64 32 29 (join 64 16 16 (join 64 8 8 prefix_r18_part64 prefix_r18_part72) (join 80 8 8 prefix_r18_part80 prefix_r18_part88)) (join 96 16 13 (join 96 8 8 prefix_r18_part96 prefix_r18_part104) (join 112 8 5 prefix_r18_part112 prefix_r18_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r19_part0 : ∀ i ∈ List.range 8, PrefixAt 19 (0+i) := by decide +kernel

theorem prefix_r19_part8 : ∀ i ∈ List.range 8, PrefixAt 19 (8+i) := by decide +kernel

theorem prefix_r19_part16 : ∀ i ∈ List.range 8, PrefixAt 19 (16+i) := by decide +kernel

theorem prefix_r19_part24 : ∀ i ∈ List.range 8, PrefixAt 19 (24+i) := by decide +kernel

theorem prefix_r19_part32 : ∀ i ∈ List.range 8, PrefixAt 19 (32+i) := by decide +kernel

theorem prefix_r19_part40 : ∀ i ∈ List.range 8, PrefixAt 19 (40+i) := by decide +kernel

theorem prefix_r19_part48 : ∀ i ∈ List.range 8, PrefixAt 19 (48+i) := by decide +kernel

theorem prefix_r19_part56 : ∀ i ∈ List.range 8, PrefixAt 19 (56+i) := by decide +kernel

theorem prefix_r19_part64 : ∀ i ∈ List.range 8, PrefixAt 19 (64+i) := by decide +kernel

theorem prefix_r19_part72 : ∀ i ∈ List.range 8, PrefixAt 19 (72+i) := by decide +kernel

theorem prefix_r19_part80 : ∀ i ∈ List.range 8, PrefixAt 19 (80+i) := by decide +kernel

theorem prefix_r19_part88 : ∀ i ∈ List.range 8, PrefixAt 19 (88+i) := by decide +kernel

theorem prefix_r19_part96 : ∀ i ∈ List.range 8, PrefixAt 19 (96+i) := by decide +kernel

theorem prefix_r19_part104 : ∀ i ∈ List.range 8, PrefixAt 19 (104+i) := by decide +kernel

theorem prefix_r19_part112 : ∀ i ∈ List.range 8, PrefixAt 19 (112+i) := by decide +kernel

theorem prefix_r19_part120 : ∀ i ∈ List.range 4, PrefixAt 19 (120+i) := by decide +kernel

theorem prefix_r19 (V : ℕ) (hV : V ∈ List.range 124) : PrefixAt 19 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 19 V)
  have h := (join 0 64 60 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r19_part0 prefix_r19_part8) (join 16 8 8 prefix_r19_part16 prefix_r19_part24)) (join 32 16 16 (join 32 8 8 prefix_r19_part32 prefix_r19_part40) (join 48 8 8 prefix_r19_part48 prefix_r19_part56))) (join 64 32 28 (join 64 16 16 (join 64 8 8 prefix_r19_part64 prefix_r19_part72) (join 80 8 8 prefix_r19_part80 prefix_r19_part88)) (join 96 16 12 (join 96 8 8 prefix_r19_part96 prefix_r19_part104) (join 112 8 4 prefix_r19_part112 prefix_r19_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r20_part0 : ∀ i ∈ List.range 8, PrefixAt 20 (0+i) := by decide +kernel

theorem prefix_r20_part8 : ∀ i ∈ List.range 8, PrefixAt 20 (8+i) := by decide +kernel

theorem prefix_r20_part16 : ∀ i ∈ List.range 8, PrefixAt 20 (16+i) := by decide +kernel

theorem prefix_r20_part24 : ∀ i ∈ List.range 8, PrefixAt 20 (24+i) := by decide +kernel

theorem prefix_r20_part32 : ∀ i ∈ List.range 8, PrefixAt 20 (32+i) := by decide +kernel

theorem prefix_r20_part40 : ∀ i ∈ List.range 8, PrefixAt 20 (40+i) := by decide +kernel

theorem prefix_r20_part48 : ∀ i ∈ List.range 8, PrefixAt 20 (48+i) := by decide +kernel

theorem prefix_r20_part56 : ∀ i ∈ List.range 8, PrefixAt 20 (56+i) := by decide +kernel

theorem prefix_r20_part64 : ∀ i ∈ List.range 8, PrefixAt 20 (64+i) := by decide +kernel

theorem prefix_r20_part72 : ∀ i ∈ List.range 8, PrefixAt 20 (72+i) := by decide +kernel

theorem prefix_r20_part80 : ∀ i ∈ List.range 8, PrefixAt 20 (80+i) := by decide +kernel

theorem prefix_r20_part88 : ∀ i ∈ List.range 8, PrefixAt 20 (88+i) := by decide +kernel

theorem prefix_r20_part96 : ∀ i ∈ List.range 8, PrefixAt 20 (96+i) := by decide +kernel

theorem prefix_r20_part104 : ∀ i ∈ List.range 8, PrefixAt 20 (104+i) := by decide +kernel

theorem prefix_r20_part112 : ∀ i ∈ List.range 8, PrefixAt 20 (112+i) := by decide +kernel

theorem prefix_r20_part120 : ∀ i ∈ List.range 3, PrefixAt 20 (120+i) := by decide +kernel

theorem prefix_r20 (V : ℕ) (hV : V ∈ List.range 123) : PrefixAt 20 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 20 V)
  have h := (join 0 64 59 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r20_part0 prefix_r20_part8) (join 16 8 8 prefix_r20_part16 prefix_r20_part24)) (join 32 16 16 (join 32 8 8 prefix_r20_part32 prefix_r20_part40) (join 48 8 8 prefix_r20_part48 prefix_r20_part56))) (join 64 32 27 (join 64 16 16 (join 64 8 8 prefix_r20_part64 prefix_r20_part72) (join 80 8 8 prefix_r20_part80 prefix_r20_part88)) (join 96 16 11 (join 96 8 8 prefix_r20_part96 prefix_r20_part104) (join 112 8 3 prefix_r20_part112 prefix_r20_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r21_part0 : ∀ i ∈ List.range 8, PrefixAt 21 (0+i) := by decide +kernel

theorem prefix_r21_part8 : ∀ i ∈ List.range 8, PrefixAt 21 (8+i) := by decide +kernel

theorem prefix_r21_part16 : ∀ i ∈ List.range 8, PrefixAt 21 (16+i) := by decide +kernel

theorem prefix_r21_part24 : ∀ i ∈ List.range 8, PrefixAt 21 (24+i) := by decide +kernel

theorem prefix_r21_part32 : ∀ i ∈ List.range 8, PrefixAt 21 (32+i) := by decide +kernel

theorem prefix_r21_part40 : ∀ i ∈ List.range 8, PrefixAt 21 (40+i) := by decide +kernel

theorem prefix_r21_part48 : ∀ i ∈ List.range 8, PrefixAt 21 (48+i) := by decide +kernel

theorem prefix_r21_part56 : ∀ i ∈ List.range 8, PrefixAt 21 (56+i) := by decide +kernel

theorem prefix_r21_part64 : ∀ i ∈ List.range 8, PrefixAt 21 (64+i) := by decide +kernel

theorem prefix_r21_part72 : ∀ i ∈ List.range 8, PrefixAt 21 (72+i) := by decide +kernel

theorem prefix_r21_part80 : ∀ i ∈ List.range 8, PrefixAt 21 (80+i) := by decide +kernel

theorem prefix_r21_part88 : ∀ i ∈ List.range 8, PrefixAt 21 (88+i) := by decide +kernel

theorem prefix_r21_part96 : ∀ i ∈ List.range 8, PrefixAt 21 (96+i) := by decide +kernel

theorem prefix_r21_part104 : ∀ i ∈ List.range 8, PrefixAt 21 (104+i) := by decide +kernel

theorem prefix_r21_part112 : ∀ i ∈ List.range 8, PrefixAt 21 (112+i) := by decide +kernel

theorem prefix_r21_part120 : ∀ i ∈ List.range 2, PrefixAt 21 (120+i) := by decide +kernel

theorem prefix_r21 (V : ℕ) (hV : V ∈ List.range 122) : PrefixAt 21 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 21 V)
  have h := (join 0 64 58 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r21_part0 prefix_r21_part8) (join 16 8 8 prefix_r21_part16 prefix_r21_part24)) (join 32 16 16 (join 32 8 8 prefix_r21_part32 prefix_r21_part40) (join 48 8 8 prefix_r21_part48 prefix_r21_part56))) (join 64 32 26 (join 64 16 16 (join 64 8 8 prefix_r21_part64 prefix_r21_part72) (join 80 8 8 prefix_r21_part80 prefix_r21_part88)) (join 96 16 10 (join 96 8 8 prefix_r21_part96 prefix_r21_part104) (join 112 8 2 prefix_r21_part112 prefix_r21_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r22_part0 : ∀ i ∈ List.range 8, PrefixAt 22 (0+i) := by decide +kernel

theorem prefix_r22_part8 : ∀ i ∈ List.range 8, PrefixAt 22 (8+i) := by decide +kernel

theorem prefix_r22_part16 : ∀ i ∈ List.range 8, PrefixAt 22 (16+i) := by decide +kernel

theorem prefix_r22_part24 : ∀ i ∈ List.range 8, PrefixAt 22 (24+i) := by decide +kernel

theorem prefix_r22_part32 : ∀ i ∈ List.range 8, PrefixAt 22 (32+i) := by decide +kernel

theorem prefix_r22_part40 : ∀ i ∈ List.range 8, PrefixAt 22 (40+i) := by decide +kernel

theorem prefix_r22_part48 : ∀ i ∈ List.range 8, PrefixAt 22 (48+i) := by decide +kernel

theorem prefix_r22_part56 : ∀ i ∈ List.range 8, PrefixAt 22 (56+i) := by decide +kernel

theorem prefix_r22_part64 : ∀ i ∈ List.range 8, PrefixAt 22 (64+i) := by decide +kernel

theorem prefix_r22_part72 : ∀ i ∈ List.range 8, PrefixAt 22 (72+i) := by decide +kernel

theorem prefix_r22_part80 : ∀ i ∈ List.range 8, PrefixAt 22 (80+i) := by decide +kernel

theorem prefix_r22_part88 : ∀ i ∈ List.range 8, PrefixAt 22 (88+i) := by decide +kernel

theorem prefix_r22_part96 : ∀ i ∈ List.range 8, PrefixAt 22 (96+i) := by decide +kernel

theorem prefix_r22_part104 : ∀ i ∈ List.range 8, PrefixAt 22 (104+i) := by decide +kernel

theorem prefix_r22_part112 : ∀ i ∈ List.range 8, PrefixAt 22 (112+i) := by decide +kernel

theorem prefix_r22_part120 : ∀ i ∈ List.range 1, PrefixAt 22 (120+i) := by decide +kernel

theorem prefix_r22 (V : ℕ) (hV : V ∈ List.range 121) : PrefixAt 22 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 22 V)
  have h := (join 0 64 57 (join 0 32 32 (join 0 16 16 (join 0 8 8 prefix_r22_part0 prefix_r22_part8) (join 16 8 8 prefix_r22_part16 prefix_r22_part24)) (join 32 16 16 (join 32 8 8 prefix_r22_part32 prefix_r22_part40) (join 48 8 8 prefix_r22_part48 prefix_r22_part56))) (join 64 32 25 (join 64 16 16 (join 64 8 8 prefix_r22_part64 prefix_r22_part72) (join 80 8 8 prefix_r22_part80 prefix_r22_part88)) (join 96 16 9 (join 96 8 8 prefix_r22_part96 prefix_r22_part104) (join 112 8 1 prefix_r22_part112 prefix_r22_part120))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r23_part0 : ∀ i ∈ List.range 8, PrefixAt 23 (0+i) := by decide +kernel

theorem prefix_r23_part8 : ∀ i ∈ List.range 8, PrefixAt 23 (8+i) := by decide +kernel

theorem prefix_r23_part16 : ∀ i ∈ List.range 8, PrefixAt 23 (16+i) := by decide +kernel

theorem prefix_r23_part24 : ∀ i ∈ List.range 8, PrefixAt 23 (24+i) := by decide +kernel

theorem prefix_r23_part32 : ∀ i ∈ List.range 8, PrefixAt 23 (32+i) := by decide +kernel

theorem prefix_r23_part40 : ∀ i ∈ List.range 8, PrefixAt 23 (40+i) := by decide +kernel

theorem prefix_r23_part48 : ∀ i ∈ List.range 8, PrefixAt 23 (48+i) := by decide +kernel

theorem prefix_r23_part56 : ∀ i ∈ List.range 8, PrefixAt 23 (56+i) := by decide +kernel

theorem prefix_r23_part64 : ∀ i ∈ List.range 8, PrefixAt 23 (64+i) := by decide +kernel

theorem prefix_r23_part72 : ∀ i ∈ List.range 8, PrefixAt 23 (72+i) := by decide +kernel

theorem prefix_r23_part80 : ∀ i ∈ List.range 8, PrefixAt 23 (80+i) := by decide +kernel

theorem prefix_r23_part88 : ∀ i ∈ List.range 8, PrefixAt 23 (88+i) := by decide +kernel

theorem prefix_r23_part96 : ∀ i ∈ List.range 8, PrefixAt 23 (96+i) := by decide +kernel

theorem prefix_r23_part104 : ∀ i ∈ List.range 8, PrefixAt 23 (104+i) := by decide +kernel

theorem prefix_r23_part112 : ∀ i ∈ List.range 8, PrefixAt 23 (112+i) := by decide +kernel

theorem prefix_r23 (V : ℕ) (hV : V ∈ List.range 120) : PrefixAt 23 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 23 V)
  have h := (join 0 56 64 (join 0 24 32 (join 0 8 16 prefix_r23_part0 (join 8 8 8 prefix_r23_part8 prefix_r23_part16)) (join 24 16 16 (join 24 8 8 prefix_r23_part24 prefix_r23_part32) (join 40 8 8 prefix_r23_part40 prefix_r23_part48))) (join 56 32 32 (join 56 16 16 (join 56 8 8 prefix_r23_part56 prefix_r23_part64) (join 72 8 8 prefix_r23_part72 prefix_r23_part80)) (join 88 16 16 (join 88 8 8 prefix_r23_part88 prefix_r23_part96) (join 104 8 8 prefix_r23_part104 prefix_r23_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r24_part0 : ∀ i ∈ List.range 8, PrefixAt 24 (0+i) := by decide +kernel

theorem prefix_r24_part8 : ∀ i ∈ List.range 8, PrefixAt 24 (8+i) := by decide +kernel

theorem prefix_r24_part16 : ∀ i ∈ List.range 8, PrefixAt 24 (16+i) := by decide +kernel

theorem prefix_r24_part24 : ∀ i ∈ List.range 8, PrefixAt 24 (24+i) := by decide +kernel

theorem prefix_r24_part32 : ∀ i ∈ List.range 8, PrefixAt 24 (32+i) := by decide +kernel

theorem prefix_r24_part40 : ∀ i ∈ List.range 8, PrefixAt 24 (40+i) := by decide +kernel

theorem prefix_r24_part48 : ∀ i ∈ List.range 8, PrefixAt 24 (48+i) := by decide +kernel

theorem prefix_r24_part56 : ∀ i ∈ List.range 8, PrefixAt 24 (56+i) := by decide +kernel

theorem prefix_r24_part64 : ∀ i ∈ List.range 8, PrefixAt 24 (64+i) := by decide +kernel

theorem prefix_r24_part72 : ∀ i ∈ List.range 8, PrefixAt 24 (72+i) := by decide +kernel

theorem prefix_r24_part80 : ∀ i ∈ List.range 8, PrefixAt 24 (80+i) := by decide +kernel

theorem prefix_r24_part88 : ∀ i ∈ List.range 8, PrefixAt 24 (88+i) := by decide +kernel

theorem prefix_r24_part96 : ∀ i ∈ List.range 8, PrefixAt 24 (96+i) := by decide +kernel

theorem prefix_r24_part104 : ∀ i ∈ List.range 8, PrefixAt 24 (104+i) := by decide +kernel

theorem prefix_r24_part112 : ∀ i ∈ List.range 7, PrefixAt 24 (112+i) := by decide +kernel

theorem prefix_r24 (V : ℕ) (hV : V ∈ List.range 119) : PrefixAt 24 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 24 V)
  have h := (join 0 56 63 (join 0 24 32 (join 0 8 16 prefix_r24_part0 (join 8 8 8 prefix_r24_part8 prefix_r24_part16)) (join 24 16 16 (join 24 8 8 prefix_r24_part24 prefix_r24_part32) (join 40 8 8 prefix_r24_part40 prefix_r24_part48))) (join 56 32 31 (join 56 16 16 (join 56 8 8 prefix_r24_part56 prefix_r24_part64) (join 72 8 8 prefix_r24_part72 prefix_r24_part80)) (join 88 16 15 (join 88 8 8 prefix_r24_part88 prefix_r24_part96) (join 104 8 7 prefix_r24_part104 prefix_r24_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r25_part0 : ∀ i ∈ List.range 8, PrefixAt 25 (0+i) := by decide +kernel

theorem prefix_r25_part8 : ∀ i ∈ List.range 8, PrefixAt 25 (8+i) := by decide +kernel

theorem prefix_r25_part16 : ∀ i ∈ List.range 8, PrefixAt 25 (16+i) := by decide +kernel

theorem prefix_r25_part24 : ∀ i ∈ List.range 8, PrefixAt 25 (24+i) := by decide +kernel

theorem prefix_r25_part32 : ∀ i ∈ List.range 8, PrefixAt 25 (32+i) := by decide +kernel

theorem prefix_r25_part40 : ∀ i ∈ List.range 8, PrefixAt 25 (40+i) := by decide +kernel

theorem prefix_r25_part48 : ∀ i ∈ List.range 8, PrefixAt 25 (48+i) := by decide +kernel

theorem prefix_r25_part56 : ∀ i ∈ List.range 8, PrefixAt 25 (56+i) := by decide +kernel

theorem prefix_r25_part64 : ∀ i ∈ List.range 8, PrefixAt 25 (64+i) := by decide +kernel

theorem prefix_r25_part72 : ∀ i ∈ List.range 8, PrefixAt 25 (72+i) := by decide +kernel

theorem prefix_r25_part80 : ∀ i ∈ List.range 8, PrefixAt 25 (80+i) := by decide +kernel

theorem prefix_r25_part88 : ∀ i ∈ List.range 8, PrefixAt 25 (88+i) := by decide +kernel

theorem prefix_r25_part96 : ∀ i ∈ List.range 8, PrefixAt 25 (96+i) := by decide +kernel

theorem prefix_r25_part104 : ∀ i ∈ List.range 8, PrefixAt 25 (104+i) := by decide +kernel

theorem prefix_r25_part112 : ∀ i ∈ List.range 6, PrefixAt 25 (112+i) := by decide +kernel

theorem prefix_r25 (V : ℕ) (hV : V ∈ List.range 118) : PrefixAt 25 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 25 V)
  have h := (join 0 56 62 (join 0 24 32 (join 0 8 16 prefix_r25_part0 (join 8 8 8 prefix_r25_part8 prefix_r25_part16)) (join 24 16 16 (join 24 8 8 prefix_r25_part24 prefix_r25_part32) (join 40 8 8 prefix_r25_part40 prefix_r25_part48))) (join 56 32 30 (join 56 16 16 (join 56 8 8 prefix_r25_part56 prefix_r25_part64) (join 72 8 8 prefix_r25_part72 prefix_r25_part80)) (join 88 16 14 (join 88 8 8 prefix_r25_part88 prefix_r25_part96) (join 104 8 6 prefix_r25_part104 prefix_r25_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r26_part0 : ∀ i ∈ List.range 8, PrefixAt 26 (0+i) := by decide +kernel

theorem prefix_r26_part8 : ∀ i ∈ List.range 8, PrefixAt 26 (8+i) := by decide +kernel

theorem prefix_r26_part16 : ∀ i ∈ List.range 8, PrefixAt 26 (16+i) := by decide +kernel

theorem prefix_r26_part24 : ∀ i ∈ List.range 8, PrefixAt 26 (24+i) := by decide +kernel

theorem prefix_r26_part32 : ∀ i ∈ List.range 8, PrefixAt 26 (32+i) := by decide +kernel

theorem prefix_r26_part40 : ∀ i ∈ List.range 8, PrefixAt 26 (40+i) := by decide +kernel

theorem prefix_r26_part48 : ∀ i ∈ List.range 8, PrefixAt 26 (48+i) := by decide +kernel

theorem prefix_r26_part56 : ∀ i ∈ List.range 8, PrefixAt 26 (56+i) := by decide +kernel

theorem prefix_r26_part64 : ∀ i ∈ List.range 8, PrefixAt 26 (64+i) := by decide +kernel

theorem prefix_r26_part72 : ∀ i ∈ List.range 8, PrefixAt 26 (72+i) := by decide +kernel

theorem prefix_r26_part80 : ∀ i ∈ List.range 8, PrefixAt 26 (80+i) := by decide +kernel

theorem prefix_r26_part88 : ∀ i ∈ List.range 8, PrefixAt 26 (88+i) := by decide +kernel

theorem prefix_r26_part96 : ∀ i ∈ List.range 8, PrefixAt 26 (96+i) := by decide +kernel

theorem prefix_r26_part104 : ∀ i ∈ List.range 8, PrefixAt 26 (104+i) := by decide +kernel

theorem prefix_r26_part112 : ∀ i ∈ List.range 5, PrefixAt 26 (112+i) := by decide +kernel

theorem prefix_r26 (V : ℕ) (hV : V ∈ List.range 117) : PrefixAt 26 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 26 V)
  have h := (join 0 56 61 (join 0 24 32 (join 0 8 16 prefix_r26_part0 (join 8 8 8 prefix_r26_part8 prefix_r26_part16)) (join 24 16 16 (join 24 8 8 prefix_r26_part24 prefix_r26_part32) (join 40 8 8 prefix_r26_part40 prefix_r26_part48))) (join 56 32 29 (join 56 16 16 (join 56 8 8 prefix_r26_part56 prefix_r26_part64) (join 72 8 8 prefix_r26_part72 prefix_r26_part80)) (join 88 16 13 (join 88 8 8 prefix_r26_part88 prefix_r26_part96) (join 104 8 5 prefix_r26_part104 prefix_r26_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r27_part0 : ∀ i ∈ List.range 8, PrefixAt 27 (0+i) := by decide +kernel

theorem prefix_r27_part8 : ∀ i ∈ List.range 8, PrefixAt 27 (8+i) := by decide +kernel

theorem prefix_r27_part16 : ∀ i ∈ List.range 8, PrefixAt 27 (16+i) := by decide +kernel

theorem prefix_r27_part24 : ∀ i ∈ List.range 8, PrefixAt 27 (24+i) := by decide +kernel

theorem prefix_r27_part32 : ∀ i ∈ List.range 8, PrefixAt 27 (32+i) := by decide +kernel

theorem prefix_r27_part40 : ∀ i ∈ List.range 8, PrefixAt 27 (40+i) := by decide +kernel

theorem prefix_r27_part48 : ∀ i ∈ List.range 8, PrefixAt 27 (48+i) := by decide +kernel

theorem prefix_r27_part56 : ∀ i ∈ List.range 8, PrefixAt 27 (56+i) := by decide +kernel

theorem prefix_r27_part64 : ∀ i ∈ List.range 8, PrefixAt 27 (64+i) := by decide +kernel

theorem prefix_r27_part72 : ∀ i ∈ List.range 8, PrefixAt 27 (72+i) := by decide +kernel

theorem prefix_r27_part80 : ∀ i ∈ List.range 8, PrefixAt 27 (80+i) := by decide +kernel

theorem prefix_r27_part88 : ∀ i ∈ List.range 8, PrefixAt 27 (88+i) := by decide +kernel

theorem prefix_r27_part96 : ∀ i ∈ List.range 8, PrefixAt 27 (96+i) := by decide +kernel

theorem prefix_r27_part104 : ∀ i ∈ List.range 8, PrefixAt 27 (104+i) := by decide +kernel

theorem prefix_r27_part112 : ∀ i ∈ List.range 4, PrefixAt 27 (112+i) := by decide +kernel

theorem prefix_r27 (V : ℕ) (hV : V ∈ List.range 116) : PrefixAt 27 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 27 V)
  have h := (join 0 56 60 (join 0 24 32 (join 0 8 16 prefix_r27_part0 (join 8 8 8 prefix_r27_part8 prefix_r27_part16)) (join 24 16 16 (join 24 8 8 prefix_r27_part24 prefix_r27_part32) (join 40 8 8 prefix_r27_part40 prefix_r27_part48))) (join 56 32 28 (join 56 16 16 (join 56 8 8 prefix_r27_part56 prefix_r27_part64) (join 72 8 8 prefix_r27_part72 prefix_r27_part80)) (join 88 16 12 (join 88 8 8 prefix_r27_part88 prefix_r27_part96) (join 104 8 4 prefix_r27_part104 prefix_r27_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r28_part0 : ∀ i ∈ List.range 8, PrefixAt 28 (0+i) := by decide +kernel

theorem prefix_r28_part8 : ∀ i ∈ List.range 8, PrefixAt 28 (8+i) := by decide +kernel

theorem prefix_r28_part16 : ∀ i ∈ List.range 8, PrefixAt 28 (16+i) := by decide +kernel

theorem prefix_r28_part24 : ∀ i ∈ List.range 8, PrefixAt 28 (24+i) := by decide +kernel

theorem prefix_r28_part32 : ∀ i ∈ List.range 8, PrefixAt 28 (32+i) := by decide +kernel

theorem prefix_r28_part40 : ∀ i ∈ List.range 8, PrefixAt 28 (40+i) := by decide +kernel

theorem prefix_r28_part48 : ∀ i ∈ List.range 8, PrefixAt 28 (48+i) := by decide +kernel

theorem prefix_r28_part56 : ∀ i ∈ List.range 8, PrefixAt 28 (56+i) := by decide +kernel

theorem prefix_r28_part64 : ∀ i ∈ List.range 8, PrefixAt 28 (64+i) := by decide +kernel

theorem prefix_r28_part72 : ∀ i ∈ List.range 8, PrefixAt 28 (72+i) := by decide +kernel

theorem prefix_r28_part80 : ∀ i ∈ List.range 8, PrefixAt 28 (80+i) := by decide +kernel

theorem prefix_r28_part88 : ∀ i ∈ List.range 8, PrefixAt 28 (88+i) := by decide +kernel

theorem prefix_r28_part96 : ∀ i ∈ List.range 8, PrefixAt 28 (96+i) := by decide +kernel

theorem prefix_r28_part104 : ∀ i ∈ List.range 8, PrefixAt 28 (104+i) := by decide +kernel

theorem prefix_r28_part112 : ∀ i ∈ List.range 3, PrefixAt 28 (112+i) := by decide +kernel

theorem prefix_r28 (V : ℕ) (hV : V ∈ List.range 115) : PrefixAt 28 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 28 V)
  have h := (join 0 56 59 (join 0 24 32 (join 0 8 16 prefix_r28_part0 (join 8 8 8 prefix_r28_part8 prefix_r28_part16)) (join 24 16 16 (join 24 8 8 prefix_r28_part24 prefix_r28_part32) (join 40 8 8 prefix_r28_part40 prefix_r28_part48))) (join 56 32 27 (join 56 16 16 (join 56 8 8 prefix_r28_part56 prefix_r28_part64) (join 72 8 8 prefix_r28_part72 prefix_r28_part80)) (join 88 16 11 (join 88 8 8 prefix_r28_part88 prefix_r28_part96) (join 104 8 3 prefix_r28_part104 prefix_r28_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r29_part0 : ∀ i ∈ List.range 8, PrefixAt 29 (0+i) := by decide +kernel

theorem prefix_r29_part8 : ∀ i ∈ List.range 8, PrefixAt 29 (8+i) := by decide +kernel

theorem prefix_r29_part16 : ∀ i ∈ List.range 8, PrefixAt 29 (16+i) := by decide +kernel

theorem prefix_r29_part24 : ∀ i ∈ List.range 8, PrefixAt 29 (24+i) := by decide +kernel

theorem prefix_r29_part32 : ∀ i ∈ List.range 8, PrefixAt 29 (32+i) := by decide +kernel

theorem prefix_r29_part40 : ∀ i ∈ List.range 8, PrefixAt 29 (40+i) := by decide +kernel

theorem prefix_r29_part48 : ∀ i ∈ List.range 8, PrefixAt 29 (48+i) := by decide +kernel

theorem prefix_r29_part56 : ∀ i ∈ List.range 8, PrefixAt 29 (56+i) := by decide +kernel

theorem prefix_r29_part64 : ∀ i ∈ List.range 8, PrefixAt 29 (64+i) := by decide +kernel

theorem prefix_r29_part72 : ∀ i ∈ List.range 8, PrefixAt 29 (72+i) := by decide +kernel

theorem prefix_r29_part80 : ∀ i ∈ List.range 8, PrefixAt 29 (80+i) := by decide +kernel

theorem prefix_r29_part88 : ∀ i ∈ List.range 8, PrefixAt 29 (88+i) := by decide +kernel

theorem prefix_r29_part96 : ∀ i ∈ List.range 8, PrefixAt 29 (96+i) := by decide +kernel

theorem prefix_r29_part104 : ∀ i ∈ List.range 8, PrefixAt 29 (104+i) := by decide +kernel

theorem prefix_r29_part112 : ∀ i ∈ List.range 2, PrefixAt 29 (112+i) := by decide +kernel

theorem prefix_r29 (V : ℕ) (hV : V ∈ List.range 114) : PrefixAt 29 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 29 V)
  have h := (join 0 56 58 (join 0 24 32 (join 0 8 16 prefix_r29_part0 (join 8 8 8 prefix_r29_part8 prefix_r29_part16)) (join 24 16 16 (join 24 8 8 prefix_r29_part24 prefix_r29_part32) (join 40 8 8 prefix_r29_part40 prefix_r29_part48))) (join 56 32 26 (join 56 16 16 (join 56 8 8 prefix_r29_part56 prefix_r29_part64) (join 72 8 8 prefix_r29_part72 prefix_r29_part80)) (join 88 16 10 (join 88 8 8 prefix_r29_part88 prefix_r29_part96) (join 104 8 2 prefix_r29_part104 prefix_r29_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r30_part0 : ∀ i ∈ List.range 8, PrefixAt 30 (0+i) := by decide +kernel

theorem prefix_r30_part8 : ∀ i ∈ List.range 8, PrefixAt 30 (8+i) := by decide +kernel

theorem prefix_r30_part16 : ∀ i ∈ List.range 8, PrefixAt 30 (16+i) := by decide +kernel

theorem prefix_r30_part24 : ∀ i ∈ List.range 8, PrefixAt 30 (24+i) := by decide +kernel

theorem prefix_r30_part32 : ∀ i ∈ List.range 8, PrefixAt 30 (32+i) := by decide +kernel

theorem prefix_r30_part40 : ∀ i ∈ List.range 8, PrefixAt 30 (40+i) := by decide +kernel

theorem prefix_r30_part48 : ∀ i ∈ List.range 8, PrefixAt 30 (48+i) := by decide +kernel

theorem prefix_r30_part56 : ∀ i ∈ List.range 8, PrefixAt 30 (56+i) := by decide +kernel

theorem prefix_r30_part64 : ∀ i ∈ List.range 8, PrefixAt 30 (64+i) := by decide +kernel

theorem prefix_r30_part72 : ∀ i ∈ List.range 8, PrefixAt 30 (72+i) := by decide +kernel

theorem prefix_r30_part80 : ∀ i ∈ List.range 8, PrefixAt 30 (80+i) := by decide +kernel

theorem prefix_r30_part88 : ∀ i ∈ List.range 8, PrefixAt 30 (88+i) := by decide +kernel

theorem prefix_r30_part96 : ∀ i ∈ List.range 8, PrefixAt 30 (96+i) := by decide +kernel

theorem prefix_r30_part104 : ∀ i ∈ List.range 8, PrefixAt 30 (104+i) := by decide +kernel

theorem prefix_r30_part112 : ∀ i ∈ List.range 1, PrefixAt 30 (112+i) := by decide +kernel

theorem prefix_r30 (V : ℕ) (hV : V ∈ List.range 113) : PrefixAt 30 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 30 V)
  have h := (join 0 56 57 (join 0 24 32 (join 0 8 16 prefix_r30_part0 (join 8 8 8 prefix_r30_part8 prefix_r30_part16)) (join 24 16 16 (join 24 8 8 prefix_r30_part24 prefix_r30_part32) (join 40 8 8 prefix_r30_part40 prefix_r30_part48))) (join 56 32 25 (join 56 16 16 (join 56 8 8 prefix_r30_part56 prefix_r30_part64) (join 72 8 8 prefix_r30_part72 prefix_r30_part80)) (join 88 16 9 (join 88 8 8 prefix_r30_part88 prefix_r30_part96) (join 104 8 1 prefix_r30_part104 prefix_r30_part112))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseChecks Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefix_r31_part0 : ∀ i ∈ List.range 8, PrefixAt 31 (0+i) := by decide +kernel

theorem prefix_r31_part8 : ∀ i ∈ List.range 8, PrefixAt 31 (8+i) := by decide +kernel

theorem prefix_r31_part16 : ∀ i ∈ List.range 8, PrefixAt 31 (16+i) := by decide +kernel

theorem prefix_r31_part24 : ∀ i ∈ List.range 8, PrefixAt 31 (24+i) := by decide +kernel

theorem prefix_r31_part32 : ∀ i ∈ List.range 8, PrefixAt 31 (32+i) := by decide +kernel

theorem prefix_r31_part40 : ∀ i ∈ List.range 8, PrefixAt 31 (40+i) := by decide +kernel

theorem prefix_r31_part48 : ∀ i ∈ List.range 8, PrefixAt 31 (48+i) := by decide +kernel

theorem prefix_r31_part56 : ∀ i ∈ List.range 8, PrefixAt 31 (56+i) := by decide +kernel

theorem prefix_r31_part64 : ∀ i ∈ List.range 8, PrefixAt 31 (64+i) := by decide +kernel

theorem prefix_r31_part72 : ∀ i ∈ List.range 8, PrefixAt 31 (72+i) := by decide +kernel

theorem prefix_r31_part80 : ∀ i ∈ List.range 8, PrefixAt 31 (80+i) := by decide +kernel

theorem prefix_r31_part88 : ∀ i ∈ List.range 8, PrefixAt 31 (88+i) := by decide +kernel

theorem prefix_r31_part96 : ∀ i ∈ List.range 8, PrefixAt 31 (96+i) := by decide +kernel

theorem prefix_r31_part104 : ∀ i ∈ List.range 8, PrefixAt 31 (104+i) := by decide +kernel

theorem prefix_r31 (V : ℕ) (hV : V ∈ List.range 112) : PrefixAt 31 V := by
  let join := @BoundaryTailBaseFast.range_join (fun V => PrefixAt 31 V)
  have h := (join 0 56 56 (join 0 24 32 (join 0 8 16 prefix_r31_part0 (join 8 8 8 prefix_r31_part8 prefix_r31_part16)) (join 24 16 16 (join 24 8 8 prefix_r31_part24 prefix_r31_part32) (join 40 8 8 prefix_r31_part40 prefix_r31_part48))) (join 56 24 32 (join 56 8 16 prefix_r31_part56 (join 64 8 8 prefix_r31_part64 prefix_r31_part72)) (join 80 16 16 (join 80 8 8 prefix_r31_part80 prefix_r31_part88) (join 96 8 8 prefix_r31_part96 prefix_r31_part104))))
  simpa only [Nat.zero_add] using h V hV

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked

namespace ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
open Lower80811.PhaseSemantics
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false

theorem prefixReceipt : PrefixReceiptSound := by
  intro R V hR hRmax hRV
  interval_cases R <;> first
    | exact prefix_r1 V (List.mem_range.mpr (by omega))
    | exact prefix_r2 V (List.mem_range.mpr (by omega))
    | exact prefix_r3 V (List.mem_range.mpr (by omega))
    | exact prefix_r4 V (List.mem_range.mpr (by omega))
    | exact prefix_r5 V (List.mem_range.mpr (by omega))
    | exact prefix_r6 V (List.mem_range.mpr (by omega))
    | exact prefix_r7 V (List.mem_range.mpr (by omega))
    | exact prefix_r8 V (List.mem_range.mpr (by omega))
    | exact prefix_r9 V (List.mem_range.mpr (by omega))
    | exact prefix_r10 V (List.mem_range.mpr (by omega))
    | exact prefix_r11 V (List.mem_range.mpr (by omega))
    | exact prefix_r12 V (List.mem_range.mpr (by omega))
    | exact prefix_r13 V (List.mem_range.mpr (by omega))
    | exact prefix_r14 V (List.mem_range.mpr (by omega))
    | exact prefix_r15 V (List.mem_range.mpr (by omega))
    | exact prefix_r16 V (List.mem_range.mpr (by omega))
    | exact prefix_r17 V (List.mem_range.mpr (by omega))
    | exact prefix_r18 V (List.mem_range.mpr (by omega))
    | exact prefix_r19 V (List.mem_range.mpr (by omega))
    | exact prefix_r20 V (List.mem_range.mpr (by omega))
    | exact prefix_r21 V (List.mem_range.mpr (by omega))
    | exact prefix_r22 V (List.mem_range.mpr (by omega))
    | exact prefix_r23 V (List.mem_range.mpr (by omega))
    | exact prefix_r24 V (List.mem_range.mpr (by omega))
    | exact prefix_r25 V (List.mem_range.mpr (by omega))
    | exact prefix_r26 V (List.mem_range.mpr (by omega))
    | exact prefix_r27 V (List.mem_range.mpr (by omega))
    | exact prefix_r28 V (List.mem_range.mpr (by omega))
    | exact prefix_r29 V (List.mem_range.mpr (by omega))
    | exact prefix_r30 V (List.mem_range.mpr (by omega))
    | exact prefix_r31 V (List.mem_range.mpr (by omega))

end ProximityPrize.SubmissionLower.Lower80811.PhaseChecked
