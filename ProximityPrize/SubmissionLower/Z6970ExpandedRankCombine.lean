import ProximityPrize.SubmissionLower.Z6970ExpandedRemainderCompute
import ProximityPrize.SubmissionLower.Z6970ExpandedPlateau

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 20000

namespace ExpandedTaper6970

private theorem close_budget (a b d : ℕ) (hx : d ≤ a+b)
    (ha : 2*(a : ℤ) ≤ 277161303086208) (hb : b ≤ 220096817716710) :
    d ≤ 358677469259814 := by omega

private theorem choose_debit (atFull inPlateau : Prop) [Decidable atFull] [Decidable inPlateau]
    (r p : ℕ) (h : inPlateau → atFull) :
    (if atFull then min r p else r) ≤
      (if inPlateau then p else 0) + (if inPlateau then 0 else r) := by
  by_cases hp : inPlateau
  · simpa only [if_pos hp,if_pos (h hp),Nat.add_zero] using min_le_right r p
  · by_cases hq : atFull
    · simpa only [if_neg hp,if_pos hq,Nat.zero_add] using min_le_left r p
    · simp only [if_neg hp,if_neg hq,Nat.zero_add,le_refl]

private theorem debit_le_split (i : BlockIndex) :
    debit i ≤
      (if plateau i then ∑ z, ExpandedPivotOpt6970.charge (k := cap i.1.val) i z else 0) +
      (if plateau i then 0 else bound (cap i.1.val) i (power i)) := by
  have hk : plateau i → residualDegree (cap i.1.val) i = 1679 := by
    intro hi
    have h : 1679 ≤ i.1.val ∧ i.1.val < 3514 := hi
    simp only [residualDegree,cap,if_pos h.2,Nat.min_eq_right h.1]
  exact choose_debit (residualDegree (cap i.1.val) i = 1679) (plateau i)
    (bound (cap i.1.val) i (power i))
    (∑ z, ExpandedPivotOpt6970.charge (k := cap i.1.val) i z) hk

private theorem sum_debit_le_split (rows : Finset BlockIndex) :
    (∑ i ∈ rows, debit i) ≤
      (∑ i ∈ rows, if plateau i then ∑ z, ExpandedPivotOpt6970.charge (k := cap i.1.val) i z else 0) +
      ∑ i ∈ rows, if plateau i then 0 else bound (cap i.1.val) i (power i) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => debit_le_split i

theorem rank_budget_of_certificates
    (hp : (∑ z : ExpandedPivotOpt6970.Column, triangle z) ≤ 277161303086208)
    (hr : TaperBudget.sumRange remainderRow 4025 ≤ 220096817716710) :
    (∑ i : BlockIndex, debit i) ≤ 358677469259814 := by
  exact close_budget _ _ _ (sum_debit_le_split Finset.univ)
    (plateau_total.trans hp) (remainder_total.trans_le hr)

end ExpandedTaper6970
