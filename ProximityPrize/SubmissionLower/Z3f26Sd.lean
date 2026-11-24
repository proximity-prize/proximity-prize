import ProximityPrize.SubmissionLower.AJ
set_option Elab.async false
set_option autoImplicit true
namespace P1_6_1_5_1
open baV
open fP (qI Qg)
open scoped BigOperators
def dO (D b:ℕ) (c:ℕ→ℕ→ℕ) (m y a :ℕ) :ℕ :=
  qI (12 - 3*a) fun x =>
    (ju.n9 (D - a - x) m*ju.n9 (b + x) (b+y)*c a x) % P1.p
private theorem piece_cast (D b:ℕ) (c:ℕ→ℕ→ℕ) (m y a :ℕ) :
    (dO D b c m y a :ZMod P1.p) =
      ∑ x :Fin (12 - 3*a),((D - a - x.val).choose m:ZMod P1.p) *
        ((b + x.val).choose (b+y) :ZMod P1.p)*(c a x.val :ZMod P1.p) := by
  rw [dO,Qg,Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ZMod.natCast_mod,Nat.cast_mul,ju.n9,
    ← Nat.choose_eq_descFactorial_div_factorial]
end P1_6_1_5_1
