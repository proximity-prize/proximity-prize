import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt2
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt3
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt4
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt5
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt6
import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt7

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueSource
open P1_7 (Bank debit)
open P1_7_1_3 (blockEstimate block_append momentEstimate)
open HelperSource (WidthGuard)

open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)

theorem checked (rect : Fin 4) (i : Fin 17) :
    Checked (bank rect i) (reserve i) (excess rect) (seed rect) := by
  fin_cases i
  · exact group0_checked rect 0
  · exact group1_checked rect 0
  · exact group1_checked rect 1
  · exact group1_checked rect 2
  · exact group1_checked rect 3
  · exact group2_checked rect 0
  · exact group2_checked rect 1
  · exact group2_checked rect 2
  · exact group3_checked rect 0
  · exact group3_checked rect 1
  · exact group3_checked rect 2
  · exact group4_checked rect 0
  · exact group4_checked rect 1
  · exact group5_checked rect 0
  · exact group5_checked rect 1
  · exact group6_checked rect 0
  · exact group7_checked rect 0

theorem cutoff_fit {h : ℕ} (lo : 2339≤h) (hi : h≤33561) (rect : Fin 4) (i : Fin 17) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*179827 :=
  (checked rect i).cutoff_fit lo hi

/-- Each stage of each rectangle supplies a native avoiding row throughout
the high interval. The lower degree bounds refer to the single exceptional prime. -/
theorem rescue_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2339≤h) (hi : h≤33561) (rect : Fin 4) (i : Fin 17) {G : Jet}
    (irr : Irreducible G) (seeded : UsesSeed G) (slope : 1≤G.natDegree)
    (hs : seed rect≤seedDegree G) (hj : G.natDegree+excess rect≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q :=
  (checked rect i).avoids Crt word lo hi irr seeded slope hs hj

#print axioms checked
#print axioms cutoff_fit
#print axioms rescue_row

end Lower6960.RescueSource
