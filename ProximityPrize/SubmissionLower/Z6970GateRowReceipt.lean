import ProximityPrize.SubmissionLower.Z6970GateRowScan
import ProximityPrize.SubmissionLower.Z6970GateLeadingSparse

set_option autoImplicit false
namespace Gate6970Row
open Gate6966Cell (Gt Lv)
open ExpandedGate6970.H2307Numeric (checked checked_add mass mass_add)

structure Receipt (g : Gt) (ws : List ℕ) (lv : Lv) (lo n : ℕ) (v : ℤ) : Prop where
  cells : checked g ws lv lo n = true
  amount : mass lv lo n = v

def receiptOK (g : Gt) (ws : List ℕ) (lv : Lv) (lo n : ℕ) (v : ℤ) : Bool :=
  scan g ws lv lo n && decide (Gate6970Leading.sparseMass lv lo n = v)

theorem of_receipt (g : Gt) (ws : List ℕ) (lv : Lv) (lo n : ℕ) (v : ℤ)
    (h : receiptOK g ws lv lo n v = true) : Receipt g ws lv lo n v := by
  obtain ⟨hc,hm⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨(scan_eq g ws lv lo n).symm.trans hc,
    (Gate6970Leading.sparseMass_eq lv lo n).symm.trans (of_decide_eq_true hm)⟩

theorem join {g : Gt} {ws : List ℕ} {lv : Lv} {lo n m : ℕ} {v w : ℤ}
    (one : Receipt g ws lv lo n v) (two : Receipt g ws lv (lo+n) m w) :
    Receipt g ws lv lo (n+m) (v+w) :=
  ⟨checked_add g ws lv lo n m one.cells two.cells,
    (mass_add lv lo n m).trans (congrArg₂ (· + ·) one.amount two.amount)⟩

end Gate6970Row
