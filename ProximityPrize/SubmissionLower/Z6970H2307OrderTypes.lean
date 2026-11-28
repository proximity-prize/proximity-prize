
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 3000000

namespace Height2307Orders

structure Threshold where
  b : Nat
  j : Nat
  m : Nat
  stride : Nat

def lookup (b j : Nat) : List Threshold → Nat
  | [] => 1
  | p::rest => max (if p.b≤b ∧ p.j≤j then p.m else 1) (lookup b j rest)

end Height2307Orders
