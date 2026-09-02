/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Seventh-contact bridge from the promoted lower 67.76 architecture

The promoted `67.76` lower proof extends its quotient replacement from six
to seven successive high-band projections.  Its new terminal identity is

`D⁷(F⁷ Q)|_(F=0) = 7! * (D F)⁷ * Q`.

Consequently a regular seventh-contact branch cannot retain a nonzero
cofactor once the seventh derivative is forced to vanish.  For an upper
attack this is a useful routing theorem: any construction that tries to use
seven copies of a common locator must obtain its multiplicity from a singular
factor, from failure of the derivative-vanishing premise, or from a
challenge-dependent object.  Merely adding a seventh fixed quotient layer
does not create a new regular carrier.

This is an upper-only port of the exact promoted algebra.  It neither imports
the lower submission nor assumes its locator selection machinery.
-/

namespace ProximityPrize.SubmissionUpper.SeventhFactorBridge

open MvPolynomial

set_option maxRecDepth 30000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false

variable {K A σ : Type*} [CommRing K] [CommRing A] [NoZeroDivisors A]

noncomputable def iteratedPderiv [DecidableEq σ] (r : σ) (n : ℕ)
    (P : MvPolynomial σ K) : MvPolynomial σ K :=
  (pderiv r)^[n] P

/-- At a regular zero of `F`, vanishing of the seventh derivative of `F⁷Q`
forces the cofactor to vanish, provided `7!` is nonzero. -/
theorem map_eq_zero_of_pderiv_seven_seventh_product
    [DecidableEq σ] (φ : MvPolynomial σ K →+* A) (r : σ)
    (F Q : MvPolynomial σ K)
    (hfactorial : (5040 : A) ≠ 0)
    (hFzero : φ F = 0)
    (hregular : φ (pderiv r F) ≠ 0)
    (hseventh : φ (iteratedPderiv r 7 (F ^ 7 * Q)) = 0) :
    φ Q = 0 := by
  let dR : MvPolynomial σ K → MvPolynomial σ K := pderiv r
  let G : MvPolynomial σ K := F ^ 6 * Q
  have hG0 : φ (dR^[0] G) = 0 := by
    simp only [Function.iterate_zero_apply, G, map_mul, map_pow, hFzero,
      zero_pow (show (6 : ℕ) ≠ 0 by decide), zero_mul]
  have hG1 : φ (dR^[1] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_one, pderiv_mul, pderiv_pow, map_add, map_mul, map_pow,
      map_natCast, hFzero, zero_pow (show (6 : ℕ) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    norm_num
  have hG2 : φ (dR^[2] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, pderiv_mul, pderiv_pow, map_add, map_mul, map_pow,
      map_natCast, hFzero, zero_pow (show (6 : ℕ) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG3 : φ (dR^[3] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, pderiv_mul, pderiv_pow, map_add, map_mul, map_pow,
      map_natCast, hFzero, zero_pow (show (6 : ℕ) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG4 : φ (dR^[4] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, pderiv_mul, pderiv_pow, map_add, map_mul, map_pow,
      map_natCast, hFzero, zero_pow (show (6 : ℕ) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG5 : φ (dR^[5] G) = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, pderiv_mul, pderiv_pow, map_add, map_mul, map_pow,
      map_natCast, hFzero, zero_pow (show (6 : ℕ) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero]
    ring
  have hG6 : φ (dR^[6] G) =
      (720 : A) * (φ (dR F)) ^ 6 * φ Q := by
    simp (config := { maxSteps := 600000 }) only [dR, G,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, pderiv_mul, pderiv_pow, map_add, map_mul, map_pow,
      map_natCast, hFzero, zero_pow (show (6 : ℕ) ≠ 0 by decide),
      zero_mul, mul_zero, zero_add, add_zero, mul_add]
    ring
  change φ G = 0 at hG0
  change φ (pderiv r G) = 0 at hG1
  change φ (pderiv r (pderiv r G)) = 0 at hG2
  change φ (pderiv r (pderiv r (pderiv r G))) = 0 at hG3
  change φ (pderiv r (pderiv r (pderiv r (pderiv r G)))) = 0 at hG4
  change φ (pderiv r (pderiv r (pderiv r (pderiv r (pderiv r G))))) = 0 at hG5
  change φ (pderiv r (pderiv r (pderiv r (pderiv r (pderiv r (pderiv r G)))))) =
      (720 : A) * (φ (pderiv r F)) ^ 6 * φ Q at hG6
  have hprod : F ^ 7 * Q = F * G := by
    simp only [G]
    ring
  rw [hprod] at hseventh
  change φ (dR^[7] (F * G)) = 0 at hseventh
  have hmain :
      (5040 : A) * (φ (pderiv r F)) ^ 7 * φ Q = 0 := by
    simp (config := { maxSteps := 300000 }) only [dR,
      Function.iterate_succ_apply', Function.iterate_zero_apply,
      Function.iterate_one, pderiv_mul, map_add, map_mul, hFzero,
      hG0, hG1, hG2, hG3, hG4, hG5, hG6,
      zero_mul, mul_zero, zero_add, add_zero] at hseventh
    ring_nf at hseventh ⊢
    exact hseventh
  have hcoefficient : (5040 : A) * (φ (pderiv r F)) ^ 7 ≠ 0 :=
    mul_ne_zero hfactorial (pow_ne_zero 7 hregular)
  exact (mul_eq_zero.mp hmain).resolve_left hcoefficient

/-- The KoalaBear characteristic does not annihilate `7!`. -/
theorem koalaBear_seven_factorial_nonzero_receipt :
    5040 % 2130706433 ≠ 0 := by
  norm_num

end ProximityPrize.SubmissionUpper.SeventhFactorBridge

#print axioms ProximityPrize.SubmissionUpper.SeventhFactorBridge.map_eq_zero_of_pderiv_seven_seventh_product
