import ProximityPrize.SubmissionLower.Z6969Pack0859
import ProximityPrize.SubmissionLower.Gate6966Assm

set_option Elab.async false

-- Source: ProximityPrize.SubmissionLower.Low6969GateWitnessTransfer
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000

namespace Low6969GateCell

def transport (G : Gate6966Cell.Gt) : Gt := G

private theorem cv_eq (r : ℕ) (ws : List ℕ) (i a : ℕ) :
    Low6969GateCertCF.cvOf r ws i a = Gate6966CertCF.cvOf r ws i a := rfl

theorem allOK_transport (G : Gate6966Cell.Gt) (r : ℕ) (ws : List ℕ) (lv : Lv) (lo n : ℕ) :
    allOK (transport G) r ws lv lo n = Gate6966Cell.allOK G r ws lv lo n := by
  simp only [allOK, Gate6966Cell.allOK, okAt, Gate6966Cell.okAt, transport, cv_eq]
  rfl

private theorem level_table_eq (r w : ℕ) :
    Low6969GateClassTable.levelOK r w = Gate6966ClassTable.levelOK r w := rfl

theorem tableOK_transport (r : ℕ) (ws : List ℕ) :
    Low6969GateClassTable.tableOK r ws = Gate6966ClassTable.tableOK r ws := by
  induction ws generalizing r with
  | nil => rfl
  | cons w ws ih =>
    rw [Low6969GateClassTable.tableOK, Gate6966ClassTable.tableOK, level_table_eq, ih]

private theorem block_eq (b j t i : ℕ) : blockN b j t i = Gate6966Cell.blockN b j t i := rfl

private theorem compute_eq (b j t : ℕ) : computeN b j t = Gate6966Cell.computeN b j t := by
  unfold computeN Gate6966Cell.computeN
  rw [sumUpTo_eq, Gate6966Cell.sumUpTo_eq]
  exact Finset.sum_congr rfl (fun i _ => block_eq b j t i)

theorem lsum_transport (lv : Lv) (i : ℕ) : lsum lv i = Gate6966Cell.lsum lv i := by
  simp only [lsum, Gate6966Cell.lsum, ambLB, Gate6966Cell.ambLB, compute_eq]
  rfl

end Low6969GateCell
