/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Sixth-contact bridge from the promoted lower 67.75 architecture

The current promoted lower proof peels a common regular factor through as
many as six quotient stages.  Its terminal algebra says that, on `F = 0`, the
sixth contact derivative of `F^6 Q` is

`720 * (∂F)^6 * Q`.

This upper-only module records precisely that transferable implication.  It
does not import the lower submission and it does not claim that an upper
selector family supplies the necessary common sixth-contact identity.  In an
attack, the received pencil must still be fixed before the selector-dependent
quotient route is chosen.
-/

namespace ProximityPrize.SubmissionUpper.SixthFactorBridge

open MvPolynomial

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

variable {K A σ : Type*} [CommRing K] [CommRing A] [NoZeroDivisors A]

/-- At a regular zero of `F`, vanishing of the sixth derivative of `F^6 Q`
forces the cofactor `Q` to vanish, provided `6!` is nonzero. -/
theorem map_eq_zero_of_pderiv_six_sixth_product
    [DecidableEq σ] (φ : MvPolynomial σ K →+* A) (r : σ)
    (F Q : MvPolynomial σ K)
    (hfactorial : (720 : A) ≠ 0)
    (hFzero : φ F = 0)
    (hregular : φ (pderiv r F) ≠ 0)
    (hsixth : φ
      (pderiv r (pderiv r (pderiv r (pderiv r (pderiv r (pderiv r
        (F * (F * (F * (F * (F * (F * Q)))))))))))) = 0) :
    φ Q = 0 := by
  have hmain :
      (720 : A) * (φ (pderiv r F)) ^ 6 * φ Q = 0 := by
    have h := hsixth
    simp only [pderiv_mul, map_add, map_mul, hFzero, zero_mul, mul_zero,
      zero_add, add_zero, mul_add, add_mul] at h
    ring_nf at h ⊢
    exact h
  have hcoefficient : (720 : A) * (φ (pderiv r F)) ^ 6 ≠ 0 :=
    mul_ne_zero hfactorial (pow_ne_zero 6 hregular)
  exact (mul_eq_zero.mp hmain).resolve_left hcoefficient

end ProximityPrize.SubmissionUpper.SixthFactorBridge

#print axioms ProximityPrize.SubmissionUpper.SixthFactorBridge.map_eq_zero_of_pderiv_six_sixth_product
