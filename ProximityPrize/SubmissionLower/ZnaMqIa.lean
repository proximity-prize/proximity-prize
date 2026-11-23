import ProximityPrize.SubmissionLower.H
set_option Elab.async false
set_option autoImplicit true
namespace bRO
open cu Finset
open scoped BigOperators
private theorem sum_arithmetic (n:ℕ) (a d:ℤ) :
    (∑ t∈range n,(a - 2*d*(t:ℤ)))=(n:ℤ)*(a - d*((n:ℤ)-1)) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [sum_range_succ,ih,Nat.cast_succ]; ring
end bRO
