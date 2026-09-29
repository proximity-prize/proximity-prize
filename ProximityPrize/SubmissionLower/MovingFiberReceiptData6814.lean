import ProximityPrize.SubmissionLower.MovingFiberContextData6814R32
import ProximityPrize.SubmissionLower.MovingFiberContextData6814R37
import ProximityPrize.SubmissionLower.MovingFiberDirectKernel6814

namespace ProximityPrize.SubmissionLower.Lower80889.ReceiptData
open MovingFiberReceiptTypes6814
set_option autoImplicit false
set_option linter.all false
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
  | 37 => rows37
  | _ => #[]
def lookup (r v : Nat) : Numbers := ((rows r)[v]?).getD defaults

def rowTable : List (Array Numbers) := [rows1,rows2,rows3,rows4,rows5,rows6,rows7,rows8,rows9,rows10,rows11,rows12,rows13,rows14,rows15,rows16,rows17,rows18,rows19,rows20,rows21,rows22,rows23,rows24,rows25,rows26,rows27,rows28,rows29,rows30,rows31,rows32,rows33,rows34,rows35,rows36,rows37]
def rowsK (r : Nat) : List Numbers :=
  Nat.casesOn (motive := fun _ => List Numbers) r [] (fun r => (DirectKernel.getDK rowTable r #[]).toList)
theorem rowsK_eq (r : Nat) : rowsK r = (rows r).toList := by
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | 16 => rfl
  | 17 => rfl
  | 18 => rfl
  | 19 => rfl
  | 20 => rfl
  | 21 => rfl
  | 22 => rfl
  | 23 => rfl
  | 24 => rfl
  | 25 => rfl
  | 26 => rfl
  | 27 => rfl
  | 28 => rfl
  | 29 => rfl
  | 30 => rfl
  | 31 => rfl
  | 32 => rfl
  | 33 => rfl
  | 34 => rfl
  | 35 => rfl
  | 36 => rfl
  | 37 => rfl
  | _+38 => rfl
def lookupK (r v : Nat) : Numbers := DirectKernel.getDK (rowsK r) v defaults
theorem lookupK_eq (r v : Nat) : lookupK r v = lookup r v := by
  rw [lookupK, rowsK_eq, DirectKernel.getDK_eq, Array.getElem?_toList]
  rfl

def rowContext (r v : Nat) : PhaseRows.PhaseRowContext := context r v (lookup r v) (lookup (r-1) v)
def baseCap (p : RCN095.FlagDegree) : Nat := (lookup p.all p.yz).base.evalAt p.zOnly

def storedPrefix (r v j : Nat) : Nat := ((lookup r v).prefixValues[j]?).getD 0

structure At (r v : Nat) : Prop where
  single : SingleValid r v (lookup r v)
  base : BaseValid (lookup r v).base r v (10715-r-v) 0 (lookup r v).baseChoices
  threshold : ThresholdsValid r v (lookup r v)
  phases : PhaseRows.RowRunsValid (rowContext r v) (lookup r v).phaseRuns
  ledger : LedgerAudit.RunsValid (rowContext r v) 0 (lookup r v).ledgerRuns
  prefixR : ∀ j : Fin 10, storedPrefix (r-1) v j.val ≤ storedPrefix r v j.val
  prefixV : 1≤v → ∀ j : Fin 10, storedPrefix r (v-1) j.val ≤ storedPrefix r v j.val

def Receipt : Prop := ∀ r v, 1≤r → r≤37 → r+v≤175 → At r v

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

/-- A receipt row from the kernel-fast check on the stored rows themselves. -/
theorem At.ofK {r v : Nat}
    (h : DirectKernel.directChecksK r v (lookupK r v) (lookupK (r-1) v) (lookupK r (v-1)) = true) :
    At r v := by
  rw [lookupK_eq, lookupK_eq, lookupK_eq] at h
  exact at_of_direct (DirectAt.ofK h) rfl rfl (fun _ => rfl)

end ProximityPrize.SubmissionLower.Lower80889.ReceiptData
