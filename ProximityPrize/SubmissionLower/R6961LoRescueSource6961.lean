import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt0
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt1
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt2
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt3
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt4
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt5
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt6
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt7
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt8
import ProximityPrize.SubmissionLower.R6961LoRescueSourceReceipt9

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueSource
open P1_7 (Bank debit)
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)

theorem checked (rect : Fin 10) (i : Fin 17) (h : 6 ≤ rect.val ∨ i ≠ 0) :
    Checked (bank rect i) (reserve i) (excess rect) (seed rect) := by
  fin_cases rect
  · exact rect0_checked i (h.resolve_left (by decide))
  · exact rect1_checked i (h.resolve_left (by decide))
  · exact rect2_checked i (h.resolve_left (by decide))
  · exact rect3_checked i (h.resolve_left (by decide))
  · exact rect4_checked i (h.resolve_left (by decide))
  · exact rect5_checked i (h.resolve_left (by decide))
  · exact rect6_checked i
  · exact rect7_checked i
  · exact rect8_checked i
  · exact rect9_checked i

theorem cutoff_fit {h : ℕ} (lo : 2346≤h) (hi : h≤2449) (rect : Fin 10) (i : Fin 17)
    (hok : 6 ≤ rect.val ∨ i ≠ 0) :
    cutoff h rect i+2*h*(reserve i)<(bank rect i).shape.m*179808 :=
  (checked rect i hok).cutoff_fit lo hi

theorem rescue_row {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2346≤h) (hi : h≤2449) (rect : Fin 10) (i : Fin 17) (hok : 6 ≤ rect.val ∨ i ≠ 0) {G : Jet}
    (irr : Irreducible G) (seeded : UsesSeed G) (slope : 1≤G.natDegree)
    (hs : seed rect≤seedDegree G) (hj : G.natDegree+excess rect≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q :=
  (checked rect i hok).avoids Crt word lo hi irr seeded slope hs hj

end Lower6961.Lo.RescueSource
