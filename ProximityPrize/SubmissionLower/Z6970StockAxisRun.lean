import Mathlib.Data.Nat.Basic

set_option autoImplicit false

namespace Research6970.StockAxis

def Run (P : ℕ → Prop) : ℕ → ℕ → Prop
  | _, 0 => True
  | lo, n+1 => P lo ∧ Run P (lo+1) n

theorem atIndex {P : ℕ → Prop} {lo n a : ℕ}
    (run : Run P lo n) (left : lo ≤ a) (right : a < lo+n) : P a := by
  induction n generalizing lo with
  | zero =>
    exact False.elim (Nat.not_lt_of_ge left (by simpa only [Nat.add_zero] using right))
  | succ n ih =>
    change P lo ∧ Run P (lo+1) n at run
    by_cases atStart : a = lo
    · subst a
      exact run.1
    · have next : lo+1 ≤ a := Nat.succ_le_of_lt (lt_of_le_of_ne left (Ne.symm atStart))
      have nextBound : a < lo+1+n := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using right
      exact ih run.2 next nextBound

end Research6970.StockAxis
