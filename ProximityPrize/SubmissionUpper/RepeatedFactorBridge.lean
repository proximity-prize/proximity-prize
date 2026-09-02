/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# A second-jet bridge across a repeated regular factor

The lower track's `67.65` step introduced a recursive quotient alternative:
if every first quotient is still divisible by a fixed factor `F`, one obtains
`F ^ 2 * Q` and differentiates twice in the contact direction.  After
specializing to the regular locus `F = 0`, only

`2 * (partial F) ^ 2 * Q`

survives.  This upper-only module records that transferable algebra without
importing the lower submission.  It is deliberately a bridge, not an upper
certificate: using it in an attack still requires a large fixed-domain family
on which the second jet vanishes.
-/

namespace ProximityPrize.SubmissionUpper.RepeatedFactorBridge

open MvPolynomial

variable {K A σ : Type*} [CommRing K] [CommRing A] [NoZeroDivisors A]

/-- On the regular zero locus of `F`, vanishing of the second derivative of
`F * (F * Q)` forces the cofactor `Q` to vanish.  The map `φ` abstracts the
specialization used by a candidate polynomial and challenge. -/
theorem map_eq_zero_of_pderiv_two_square_product
    [DecidableEq σ] (φ : MvPolynomial σ K →+* A) (r : σ)
    (F Q : MvPolynomial σ K)
    (htwo : (2 : A) ≠ 0)
    (hFzero : φ F = 0)
    (hregular : φ (pderiv r F) ≠ 0)
    (hsecond : φ (pderiv r (pderiv r (F * (F * Q)))) = 0) :
    φ Q = 0 := by
  have hmain :
      (2 : A) * (φ (pderiv r F) * φ (pderiv r F)) * φ Q = 0 := by
    simpa only [pderiv_mul, map_add, map_mul, hFzero, zero_mul, mul_zero,
      zero_add, add_zero, two_mul, add_mul, mul_assoc] using hsecond
  have hcoefficient :
      (2 : A) * (φ (pderiv r F) * φ (pderiv r F)) ≠ 0 :=
    mul_ne_zero htwo (mul_ne_zero hregular hregular)
  exact (mul_eq_zero.mp hmain).resolve_left hcoefficient

end ProximityPrize.SubmissionUpper.RepeatedFactorBridge

#print axioms ProximityPrize.SubmissionUpper.RepeatedFactorBridge.map_eq_zero_of_pderiv_two_square_product
