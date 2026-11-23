import ProximityPrize.SubmissionLower.Pr657Rect2435Grade01
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade02
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade03
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade04
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade05
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade06
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade07
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade08
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade09
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade10
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade11
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade12
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade13
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade14
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade15
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade16
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade17
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade18
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade19
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade20
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade21
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade22
import ProximityPrize.SubmissionLower.Pr657Rect2435Grade23
import ProximityPrize.SubmissionLower.Pr657Rect2435Axes

set_option Elab.async false

namespace Pr657Rect2435Receipts
open Pr657Rect2435Arithmetic (EndpointChecks blockSurplus blockSurplus_eq strict_of_checks surplus)
open KoalaRect (rectGain rectDebit)

theorem rectEndpoints {E : ℕ} (he : 1 ≤ E) (hu : E ≤ 23) :
    EndpointChecks terminal.shape terminal.nodeRows terminal.poleMoment 2431 E
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

theorem rectSurplusValues {E : ℕ} (he : 1 ≤ E) (hu : E ≤ 23) :
    let v:=rectWitness E
    (rectGain 179876 2431 terminal.shape E v.U v.order : ℤ) -
        (rectDebit 2431 terminal.nodeRows terminal.poleMoment v.U:ℤ)=(endpoints E).1 ∧
      (rectGain 179876 2432 terminal.shape E v.U v.order : ℤ) -
        (rectDebit 2432 terminal.nodeRows terminal.poleMoment v.U : ℤ) =
          (endpoints E).1+(endpoints E).2:=by
  change surplus 2431 terminal E (rectWitness E) = (endpoints E).1 ∧
    surplus 2432 terminal E (rectWitness E)=(endpoints E).1+(endpoints E).2
  obtain ⟨_,h₀,h₁⟩:=rectEndpoints he hu
  rw [blockSurplus_eq terminal 2431 E (rectWitness E) (by decide) (by decide) (by omega)] at h₀
  change blockSurplus terminal.shape terminal.nodeRows terminal.poleMoment 2432 E (rectWitness E)=_ at h₁
  rw [blockSurplus_eq terminal 2432 E (rectWitness E) (by decide) (by decide) (by omega)] at h₁
  exact ⟨by omega,by omega⟩

theorem rect_bounds {h E : ℕ} (hl : 2431 ≤ h) (hh : h < 131071)
    (he:1≤E) (hu:E≤23) :
    rectDebit h terminal.nodeRows terminal.poleMoment (rectWitness E).U <
      rectGain 179876 h terminal.shape E (rectWitness E).U (rectWitness E).order:=by
  exact strict_of_checks hl hh (by decide) (by decide) (by omega) (rectEndpoints he hu).1

theorem rect_bounds_swap {h E : ℕ} (hl : 2431 ≤ h) (hh : h < 131071)
    (he:1≤E) (hu:E≤23) :
    rectDebit h terminal.nodeRows terminal.poleMoment (Pr657Rect2435Axes.swap (rectWitness E).U) <
      rectGain 179876 h terminal.shape E (Pr657Rect2435Axes.swap (rectWitness E).U)
        (Pr657Rect2435Axes.swap (rectWitness E).order):=by
  rw [Pr657Rect2435Axes.debit_swap,Pr657Rect2435Axes.gain_swap]
  exact rect_bounds hl hh he hu

#print axioms rect_bounds
#print axioms rect_bounds_swap
end Pr657Rect2435Receipts
