import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

set_option autoImplicit false

namespace SplitCut.StableNode

open Polynomial


/-- Evaluate the inner polynomial variable on a polynomial in the outer variable. -/
noncomputable def substitute {R : Type*} [CommRing R] (s : R[X]) : Polynomial R[X] →+* R[X] :=
  eval₂RingHom (eval₂RingHom C s) X



end SplitCut.StableNode

