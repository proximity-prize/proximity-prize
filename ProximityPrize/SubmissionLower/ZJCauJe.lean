import ProximityPrize.SubmissionLower.ZCvigsb
set_option Elab.async false
set_option autoImplicit true
namespace qaQQvid
open xE (denominator)



open aRR (DW)
open aAZ (azV)


open Finset
open scoped BigOperators
private theorem sum_den (a :ℤ) (l n:ℕ) :
   24*(∑ j∈range n,denominator (a - 1-((l+j:ℕ) :ℤ))) =
     DW (a-l) - DW (a-l-n) := by
 induction n with
 | zero=>simp
 | succ n ih =>
   rw [sum_range_succ,mul_add,ih,← azV]
   push_cast
   ring_nf
end qaQQvid
