import ProximityPrize.SubmissionLower.Z6970H2307FastGateNumeric
import ProximityPrize.SubmissionLower.Z6970H2307GatePacketOps

set_option Elab.async false
set_option autoImplicit false

namespace ExpandedGate6970.H2307Numeric

open Low6969GateCell

theorem checked_eq (G : Gt) (ws : List ℕ) (lv : Lv) (lo n : ℕ) :
    checked G ws lv lo n = allOK G 1 ws lv lo n := by
  unfold checked allOK
  congr 1
  funext d
  unfold okAt
  change (let (b,j,t,w) := lv.getD (lo+d) dflt
          Gate6966Cell.levelOKF G (lo+d+1) w b j t 80
            (fun a => some (Gate6966CertCF.cvOf 1 ws (lo+d+1) a))) = _
  rcases lv.getD (lo+d) dflt with ⟨b,j,t,w⟩
  change Gate6966Cell.levelOKF G (lo+d+1) w b j t 80
    (fun a => some (Gate6966CertCF.cvOf 1 ws (lo+d+1) a)) = _
  rw [Gate6966Cell.levelOKF_eq] <;> rfl

private theorem cap_eq (q : ℕ) : cap q = ExpandedColumns6970.gradeCap q := by
  by_cases h : q < 3514 <;> simp [cap, ExpandedColumns6970.gradeCap, ExpandedTaper6970.cap, Nat.blt_eq, h]

private theorem block_eq (b j t q : ℕ) (hq : q < Low6969GateAmb.bound b) :
    blockN b j t q = Gate6966Cell.cappedN (cap q) (min j 1679) (min t 500) := by
  have stop : Low6969GateAmb.stop b q = q+1 := by
    exact min_eq_right (Nat.succ_le_of_lt hq)
  unfold blockN Low6969GateAmb.padGrade Low6969GateAmb.start Low6969GateAmb.index
  rw [stop, Nat.add_sub_cancel, Nat.add_sub_cancel_left, min_self, ← cap_eq, min_comm 1679 j, min_comm 500 t]
  exact one_mul _

private theorem ambient_eq (b j t : ℕ) : ambient b j t = ambLB b j t := by
  unfold ambient ambLB
  cases h : (Nat.ble 4024 b && Nat.ble 1679 j && Nat.ble 500 t)
  · simp only [Bool.cond_false]
    unfold computeN
    rw [Gate6966Cell.sumUpTo_eq, sumUpTo_eq]
    apply Finset.sum_congr rfl
    intro q hq
    exact (block_eq b j t q (Finset.mem_range.mp hq)).symm
  · rfl

theorem loss_eq (lv : Lv) (i : ℕ) : loss lv i = lsum lv i := by
  unfold loss lsum defaultRow dflt
  rcases lv.getD i (4024,1679,500,0) with ⟨b,j,t,w⟩
  change (427286700047 : ℤ) - ambient b j t + w = Low6969Prices.symbolCount - ambLB b j t + w
  rw [ambient_eq] <;> rfl

theorem mass_wide_eq (lv : Lv) (n : ℕ) : mass lv 0 n = ∑ i ∈ Finset.range n, lsum lv i := by
  rw [mass_eq]
  exact Finset.sum_congr rfl (fun i _ => loss_eq lv i)

end ExpandedGate6970.H2307Numeric
