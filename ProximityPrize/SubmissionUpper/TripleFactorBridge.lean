/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# A third-jet bridge across a tripled regular factor

The lower track's proposed `67.67` architecture continues recursive quotient
peeling to `F * (F * (F * Q))`.  After specializing to the regular zero locus
of `F`, its third contact derivative reduces to

`6 * (partial F) ^ 3 * Q`.

This upper-only module records that abstract algebraic implication without
importing a lower submission.  It is a bridge rather than an upper
certificate: an attack must still provide a large family on which the third
jet vanishes.
-/

namespace ProximityPrize.SubmissionUpper.TripleFactorBridge

open MvPolynomial

variable {K A σ : Type*} [CommRing K] [CommRing A] [NoZeroDivisors A]

/-- On the regular zero locus of `F`, vanishing of the third derivative of
`F * (F * (F * Q))` forces the cofactor `Q` to vanish.  The map `φ` abstracts
the specialization used by a candidate polynomial and challenge. -/
theorem map_eq_zero_of_pderiv_three_cube_product
    [DecidableEq σ] (φ : MvPolynomial σ K →+* A) (r : σ)
    (F Q : MvPolynomial σ K)
    (hsix : (6 : A) ≠ 0)
    (hFzero : φ F = 0)
    (hregular : φ (pderiv r F) ≠ 0)
    (hthird : φ (pderiv r (pderiv r (pderiv r (F * (F * (F * Q)))))) = 0) :
    φ Q = 0 := by
  have hmain :
      (6 : A) * (φ (pderiv r F) * (φ (pderiv r F) * φ (pderiv r F))) * φ Q = 0 := by
    have h := hthird
    simp only [pderiv_mul, map_add, map_mul, hFzero, zero_mul, mul_zero,
      zero_add, add_zero] at h
    linear_combination h
  have hcoefficient :
      (6 : A) * (φ (pderiv r F) * (φ (pderiv r F) * φ (pderiv r F))) ≠ 0 :=
    mul_ne_zero hsix (mul_ne_zero hregular (mul_ne_zero hregular hregular))
  exact (mul_eq_zero.mp hmain).resolve_left hcoefficient

end ProximityPrize.SubmissionUpper.TripleFactorBridge

#print axioms
  ProximityPrize.SubmissionUpper.TripleFactorBridge.map_eq_zero_of_pderiv_three_cube_product
