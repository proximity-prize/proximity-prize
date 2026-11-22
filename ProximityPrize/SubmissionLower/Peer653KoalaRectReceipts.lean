import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade01
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade02
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade03
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade04
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade05
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade06
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade07
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade08
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade09
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade10
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade11
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade12
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade13
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade14
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade15
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade16
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade17
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade18
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade19
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade20
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade21
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade22
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade23
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade24
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade25
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade26
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade27
import ProximityPrize.SubmissionLower.Peer653KoalaRectReceiptsGrade28

/- Numerical port of KoalaRectReceipts.lean from public submission f3c5439b-d656-4814-b22e-b4515f0c95d9, revision d3db79e374b16bebd9780b96f1c1fe0c156679bc. -/
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 12000000
set_option quotPrecheck false

namespace KoalaRectReceipts
open KoalaRectArithmetic
open KoalaRect (rectDebit rectGain)
open Peer653High53 (terminal agreement)
open Peer653High53TerminalArithmetic (Parts)

private abbrev T := terminal .h2367

theorem rectChecks {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    BlockChecks T.shape T.nodeRows T.poleMoment 2390 E (rectWitness E) := by
  interval_cases E
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10
  · exact r11
  · exact r12
  · exact r13
  · exact r14
  · exact r15
  · exact r16
  · exact r17
  · exact r18
  · exact r19
  · exact r20
  · exact r21
  · exact r22
  · exact r23
  · exact r24
  · exact r25
  · exact r26
  · exact r27
  · exact r28

theorem witness_guards {E : ℕ} (hl : 1 ≤ E) (hu : E ≤ 28) :
    (rectWitness E).U 1 ≤ (rectWitness E).U 0 ∧
      (rectWitness E).U 0 + (rectWitness E).U 1 ≤ T.shape.U := by
  interval_cases E <;> decide

theorem paid_order {E : ℕ} (hl : 1 ≤ E) (hu : E < 28) :
    (rectWitness E).order 0 ≤ (rectWitness E).order 1 ∧
      (rectWitness E).order 1 ≤ (rectWitness E).order 0 + 1 ∧
      (rectWitness E).order 0 + (rectWitness E).order 1 = paidCap E + 1 := by
  interval_cases E <;> decide

theorem rect_bounds {h E : ℕ} (hl : 2390 ≤ h) (hu : h ≤ 2526)
    (hel : 1 ≤ E) (heu : E ≤ 28) :
    rectDebit h T.nodeRows T.poleMoment (rectWitness E).U <
      rectGain agreement h T.shape E (rectWitness E).U (rectWitness E).order := by
  exact strict_of_checks hl (by omega) (by decide) (by decide) (by omega) (rectChecks hel heu)

#print axioms rect_bounds

end KoalaRectReceipts
