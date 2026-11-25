import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks0
import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks1
import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks2
import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks3
import ProximityPrize.SubmissionLower.R6966ProofFarTerminalChecks4

set_option Elab.async false

namespace Lower6960.FarTerminalReceipts
open FarTerminalArithmetic

theorem checked (i : Fin 41) (pos : 0 < i.val) :
    BlockChecks terminalBank.shape terminalBank.nodeRows terminalBank.poleMoment 2500 i.val (witness i.val) := by
  fin_cases i
  · change 0 < 0 at pos; omega
  · exact receipt1
  · exact receipt2
  · exact receipt3
  · exact receipt4
  · exact receipt5
  · exact receipt6
  · exact receipt7
  · exact receipt8
  · exact receipt9
  · exact receipt10
  · exact receipt11
  · exact receipt12
  · exact receipt13
  · exact receipt14
  · exact receipt15
  · exact receipt16
  · exact receipt17
  · exact receipt18
  · exact receipt19
  · exact receipt20
  · exact receipt21
  · exact receipt22
  · exact receipt23
  · exact receipt24
  · exact receipt25
  · exact receipt26
  · exact receipt27
  · exact receipt28
  · exact receipt29
  · exact receipt30
  · exact receipt31
  · exact receipt32
  · exact receipt33
  · exact receipt34
  · exact receipt35
  · exact receipt36
  · exact receipt37
  · exact receipt38
  · exact receipt39
  · exact receipt40

theorem positive {h : ℕ} (lo : 2500 ≤ h) (hi : h ≤ 33677) (i : Fin 41) (pos : 0 < i.val) :
    KoalaRect.rectDebit h terminalBank.nodeRows terminalBank.poleMoment (witness i.val).U <
      KoalaRect.rectGain 179769 h terminalBank.shape i.val (witness i.val).U (witness i.val).order :=
  strict_of_checks lo (by omega) (by decide) (by decide) pos (checked i pos)

#print axioms positive
end Lower6960.FarTerminalReceipts
