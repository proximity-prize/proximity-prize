import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BCHKSSubstitutionVanish


/-!
# Actual contact multiplicities with an unknown derivative

Model label: gpt-5.

The slope is the derivative of the candidate polynomial, not received data.
The first theorem gives the precise Taylor-coefficient/divisibility interface
used by each local contact block. The remaining theorems show that contact
weight gives genuine polynomial root multiplicity and a vanishing bridge.

This module does not claim the bounded coefficient-space rank or the mixed
Bezout alignment theorem. Its finite contact representations are explicit
hypotheses to be supplied by the interpolation assembly.
-/

namespace ProximityPrize.SubmissionLower.ContactLocalDivisibility

open Polynomial

section LocalRing

variable {F : Type*} [CommRing F]

/-- A translated power divides a polynomial exactly when its first Taylor
coefficients vanish. In a contact block the coefficient ring itself contains
the formal slope and seed variables. -/
theorem shifted_power_dvd_iff_taylor_coeff_zero
    (P : F[X]) (x : F) (h : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ h ∣ P ↔
      ∀ j < h, (taylor x P).coeff j = 0 := by
  have hshift : taylor x ((Polynomial.X - Polynomial.C x) ^ h) =
      (Polynomial.X : F[X]) ^ h := by
    rw [taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  have hdiv := map_dvd_iff (taylorEquiv x)
    (a := ((Polynomial.X : F[X]) - Polynomial.C x) ^ h) (b := P)
  change taylor x ((Polynomial.X - Polynomial.C x) ^ h) ∣ taylor x P ↔
    (Polynomial.X - Polynomial.C x) ^ h ∣ P at hdiv
  rw [hshift] at hdiv
  exact hdiv.symm.trans (Polynomial.X_pow_dvd_iff (f := taylor x P) (n := h))

/-- The polynomial in the local variable `T` obtained from
`q(X)-q(x)-(X-x)q'(X)`. -/
noncomputable def contactResidual (P : F[X]) (x : F) : F[X] :=
  taylor x P - Polynomial.C (P.eval x) -
    Polynomial.X * taylor x P.derivative

/-- Value agreement supplies second-order contact even though the received
word contains no derivative symbols. No characteristic assumption is needed. -/
theorem X_sq_dvd_contactResidual (P : F[X]) (x : F) :
    (Polynomial.X : F[X]) ^ 2 ∣ contactResidual P x := by
  rw [X_pow_dvd_iff]
  intro j hj
  have hcases : j = 0 ∨ j = 1 := by omega
  rcases hcases with rfl | rfl
  · simp [contactResidual]
  · simp [contactResidual, coeff_X_mul]

/-- A monomial of contact weight at least `m` has true order at least `m`
after substituting any second-order contact residual. -/
theorem contact_monomial_dvd
    (A S R : F[X]) (m i j k : ℕ)
    (hS : (Polynomial.X : F[X]) ^ 2 ∣ S) (hweight : m ≤ i + 2 * j) :
    (Polynomial.X : F[X]) ^ m ∣ A * Polynomial.X ^ i * S ^ j * R ^ k := by
  have hSj : (Polynomial.X : F[X]) ^ (2 * j) ∣ S ^ j := by
    simpa only [pow_mul] using pow_dvd_pow_of_dvd hS j
  have hprod : (Polynomial.X : F[X]) ^ i * Polynomial.X ^ (2 * j) ∣
      Polynomial.X ^ i * S ^ j :=
    mul_dvd_mul (dvd_refl _) hSj
  have hsum : (Polynomial.X : F[X]) ^ (i + 2 * j) ∣
      Polynomial.X ^ i * S ^ j := by
    simpa only [pow_add] using hprod
  have hsmall : (Polynomial.X : F[X]) ^ m ∣ Polynomial.X ^ i * S ^ j :=
    (pow_dvd_pow Polynomial.X hweight).trans hsum
  have hleft : (Polynomial.X : F[X]) ^ m ∣ A * (Polynomial.X ^ i * S ^ j) :=
    dvd_mul_of_dvd_right hsmall A
  have hright : (Polynomial.X : F[X]) ^ m ∣
      (A * (Polynomial.X ^ i * S ^ j)) * R ^ k :=
    dvd_mul_of_dvd_left hleft (R ^ k)
  simpa only [mul_assoc] using hright

theorem contact_sum_dvd
    {J : Type*} (terms : Finset J) (coefficient : J → F[X])
    (tExp sExp rExp : J → ℕ) (S R : F[X]) (m : ℕ)
    (hS : (Polynomial.X : F[X]) ^ 2 ∣ S)
    (hweight : ∀ b ∈ terms, m ≤ tExp b + 2 * sExp b) :
    (Polynomial.X : F[X]) ^ m ∣
      ∑ b ∈ terms, coefficient b * Polynomial.X ^ tExp b * S ^ sExp b * R ^ rExp b := by
  apply Finset.dvd_sum
  intro b hb
  exact contact_monomial_dvd (coefficient b) S R m
    (tExp b) (sExp b) (rExp b) hS (hweight b hb)

end LocalRing

section GlobalVanishing

variable {F I J : Type*} [Field F] [DecidableEq F] [DecidableEq I]

/-- The actual root-count finish, reusable after assembling the shifted
interpolant into its finite contact expansion at each chosen agreement node. -/
theorem eq_zero_of_contact_representations
    (P H : F[X]) (nodes : I ↪ F) (support : Finset I) (m : ℕ)
    (terms : I → Finset J) (coefficient : I → J → F[X])
    (tExp sExp rExp : I → J → ℕ)
    (hweight : ∀ i ∈ support, ∀ b ∈ terms i,
      m ≤ tExp i b + 2 * sExp i b)
    (hrepresentation : ∀ i ∈ support,
      taylor (nodes i) H =
        ∑ b ∈ terms i, coefficient i b * Polynomial.X ^ tExp i b *
          (contactResidual P (nodes i)) ^ sExp i b *
          (taylor (nodes i) P.derivative) ^ rExp i b)
    (hdegree : H.natDegree < m * support.card) : H = 0 := by
  by_contra hnonzero
  have hmult : ∀ i ∈ support, m ≤ H.rootMultiplicity (nodes i) := by
    intro i hi
    have hlocal : (Polynomial.X : F[X]) ^ m ∣ taylor (nodes i) H := by
      rw [hrepresentation i hi]
      exact contact_sum_dvd (terms i) (coefficient i) (tExp i) (sExp i)
        (rExp i) (contactResidual P (nodes i))
        (taylor (nodes i) P.derivative) m
        (X_sq_dvd_contactResidual P (nodes i)) (hweight i hi)
    have hshifted : (Polynomial.X - Polynomial.C (nodes i)) ^ m ∣ H :=
      (shifted_power_dvd_iff_taylor_coeff_zero H (nodes i) m).mpr
        (X_pow_dvd_iff.mp hlocal)
    exact (Polynomial.le_rootMultiplicity_iff hnonzero).mpr hshifted
  have hbound := BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    H nodes support m hmult
  exact (Nat.not_le_of_gt hdegree) hbound

end GlobalVanishing

end ProximityPrize.SubmissionLower.ContactLocalDivisibility

#print axioms ProximityPrize.SubmissionLower.ContactLocalDivisibility.shifted_power_dvd_iff_taylor_coeff_zero
#print axioms ProximityPrize.SubmissionLower.ContactLocalDivisibility.X_sq_dvd_contactResidual
#print axioms ProximityPrize.SubmissionLower.ContactLocalDivisibility.contact_sum_dvd
#print axioms ProximityPrize.SubmissionLower.ContactLocalDivisibility.eq_zero_of_contact_representations
