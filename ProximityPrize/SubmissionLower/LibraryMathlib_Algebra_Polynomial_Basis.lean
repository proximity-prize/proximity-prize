import ProximityPrize.Benchmark.TargetLower
set_option Elab.async false
/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/




/-!
# Basis of a polynomial ring
-/

@[expose] public noncomputable section

open Module

universe u

variable (R : Type u) [Semiring R]

namespace Polynomial

/-- The monomials form a basis on `(Polynomial R)`. To get the rank of a polynomial ring,
use this and `Basis.mk_eq_rank`. -/
def basisMonomials : Basis ℕ R (Polynomial R) :=
  .ofRepr <| AddMonoidAlgebra.coeffLinearEquiv _

@[simp]
theorem coe_basisMonomials : (basisMonomials R : ℕ → (Polynomial R)) = fun s => monomial s 1 := rfl

end Polynomial
