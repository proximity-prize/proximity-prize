/- Apache-2.0. 68.36 degree-interval receipts by Bome2017 over the BitWonka and Lucieno physical bounds. -/

namespace Koala6835.Offers
set_option autoImplicit false
structure Offer where
  r : Nat
  y : Nat
  hi : Nat
  lo : Nat
  fee : Nat
def valid (w : Offer) (r e a b : Nat) : Prop := r ≤ w.r ∧ r+e ≤ w.y ∧ w.lo ≤ a ∧ b ≤ w.hi
instance (w : Offer) (r e a b : Nat) : Decidable (valid w r e a b) := by
  unfold valid
  infer_instance

end Koala6835.Offers
