import ProximityPrize.SubmissionLower.MovingFiberContextData6811R36
import ProximityPrize.SubmissionLower.MovingFiberDirectReceipt6811

namespace ProximityPrize.SubmissionLower.Lower80860.ReceiptData
open MovingFiberReceiptTypes6811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

def rows : Nat → Array Numbers
  | 1 => rows1
  | 2 => rows2
  | 3 => rows3
  | 4 => rows4
  | 5 => rows5
  | 6 => rows6
  | 7 => rows7
  | 8 => rows8
  | 9 => rows9
  | 10 => rows10
  | 11 => rows11
  | 12 => rows12
  | 13 => rows13
  | 14 => rows14
  | 15 => rows15
  | 16 => rows16
  | 17 => rows17
  | 18 => rows18
  | 19 => rows19
  | 20 => rows20
  | 21 => rows21
  | 22 => rows22
  | 23 => rows23
  | 24 => rows24
  | 25 => rows25
  | 26 => rows26
  | 27 => rows27
  | 28 => rows28
  | 29 => rows29
  | 30 => rows30
  | 31 => rows31
  | 32 => rows32
  | 33 => rows33
  | 34 => rows34
  | 35 => rows35
  | 36 => rows36
  | _ => #[]
def lookup (r v : Nat) : Numbers := ((rows r)[v]?).getD defaults

def rowContext (r v : Nat) : PhaseRows.PhaseRowContext := context r v (lookup r v) (lookup (r-1) v)
def baseCap (p : RCN095.FlagDegree) : Nat := (lookup p.all p.yz).base.evalAt p.zOnly

def storedPrefix (r v j : Nat) : Nat := ((lookup r v).prefixValues[j]?).getD 0

structure At (r v : Nat) : Prop where
  single : SingleValid r v (lookup r v)
  base : BaseValid (lookup r v).base r v (10170-r-v) 0 (lookup r v).baseChoices
  threshold : ThresholdsValid r v (lookup r v)
  phases : PhaseRows.RowRunsValid (rowContext r v) (lookup r v).phaseRuns
  ledger : LedgerAudit.RunsValid (rowContext r v) 0 (lookup r v).ledgerRuns
  prefixR : ∀ j : Fin 10, storedPrefix (r-1) v j.val ≤ storedPrefix r v j.val
  prefixV : 1≤v → ∀ j : Fin 10, storedPrefix r (v-1) j.val ≤ storedPrefix r v j.val

def Receipt : Prop := ∀ r v, 1≤r → r≤36 → r+v≤171 → At r v

theorem at_of_direct {r v : Nat} {row parent prior : Numbers}
    (h : DirectAt r v row parent prior) (he : row=lookup r v)
    (hp : parent=lookup (r-1) v) (hl : 1≤v → prior=lookup r (v-1)) : At r v := by
  subst row
  subst parent
  refine ⟨h.single,h.base,h.threshold,h.phases,h.ledger,?_,?_⟩
  · intro j
    exact h.prefixR j
  · intro hv j
    have hh := h.prefixV hv j
    rw [hl hv] at hh
    exact hh

end ProximityPrize.SubmissionLower.Lower80860.ReceiptData
