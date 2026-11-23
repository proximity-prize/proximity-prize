import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade01
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade02
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade03
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade04
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade05
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade06
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade07
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade08
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade09
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade10
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade11
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade12
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade13
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade14
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade15
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade16
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade17
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade18
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade19
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade20
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade21
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade22
import ProximityPrize.SubmissionLower.KoalaH2430TerminalGrade23
import ProximityPrize.SubmissionLower.Pr657Rect2435Axes

set_option Elab.async false

namespace KoalaH2430Terminal
open Pr657Rect2435Arithmetic (EndpointChecks blockSurplus blockSurplus_eq strict_of_checks surplus)
open KoalaRect (rectGain rectDebit)

theorem rectEndpoints {E : ℕ} (he : 1 ≤ E) (hu : E ≤ 23) :
    EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2430 E
      (rectWitness E) (endpoints E).1 (endpoints E).2:=by
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

theorem rect_bounds {h E : ℕ} (hl : 2430 ≤ h) (hh : h < 131071)
    (he:1≤E) (hu:E≤23) :
    rectDebit h terminal.nodeRows terminal.poleMoment (rectWitness E).U <
      rectGain 179876 h terminal.shape E (rectWitness E).U (rectWitness E).order:=by
  exact strict_of_checks hl hh (by decide) (by decide) (by omega) (rectEndpoints he hu).1

theorem rect_bounds_swap {h E : ℕ} (hl : 2430 ≤ h) (hh : h < 131071)
    (he:1≤E) (hu:E≤23) :
    rectDebit h terminal.nodeRows terminal.poleMoment (Pr657Rect2435Axes.swap (rectWitness E).U) <
      rectGain 179876 h terminal.shape E (Pr657Rect2435Axes.swap (rectWitness E).U)
        (Pr657Rect2435Axes.swap (rectWitness E).order):=by
  rw [Pr657Rect2435Axes.debit_swap,Pr657Rect2435Axes.gain_swap]
  exact rect_bounds hl hh he hu

#print axioms rect_bounds
#print axioms rect_bounds_swap
end KoalaH2430Terminal
