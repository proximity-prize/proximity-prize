/- Apache-2.0. Bome2017. Physical formulas are those of Lucieno, BitWonka and the 68.33 accepted construction. -/
import ProximityPrize.SubmissionLower.Night6836PureOffers
namespace Koala6836.PureOffers
theorem advance {P: Nat→Prop} {n:Nat} (h:∀k,k<n→P k) (v:P n) :
    ∀ k, k<n+1→P k := by
  intro k hk
  cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
  | inl hlt => exact h _ hlt
  | inr he => cases he; exact v
theorem empty {P:Nat→Prop} : ∀k,k<0→P k := fun k h=>False.elim (Nat.not_lt_zero k h)
end Koala6836.PureOffers
