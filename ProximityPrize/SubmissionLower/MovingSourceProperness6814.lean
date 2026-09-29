import ProximityPrize.SubmissionLower.MovingSourceClearing6814

/-! Clearing cannot create a common prime factor away from the clearing
denominator. This is proved by the inverse affine substitution, before
specializing the moving target. -/
namespace ProximityPrize.SubmissionLower.MovingSourceProperness6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MovingSourceClearing6814

section GCD
variable {A : Type*} [CommMonoidWithZero A] [GCDMonoid A]

theorem common_dvd_scalar (a p q d : A) (h : IsRelPrime p q)
    (hp : d ∣ a*p) (hq : d ∣ a*q) : d ∣ a := by
  have hg : IsUnit (gcd p q) := h (gcd_dvd_left p q) (gcd_dvd_right p q)
  have hh : d ∣ a*gcd p q := (dvd_gcd hp hq).trans (gcd_mul_left' a p q).dvd
  exact hg.dvd_mul_right.mp hh

end GCD

section Polynomial
variable {R : Type*} [CommRing R] [IsDomain R] [GCDMonoid (Polynomial R)]

theorem inverseSubstitution_degree (P : Polynomial R) (h q : R) (hh : h≠0) :
    (inverseSubstitution h q P).natDegree=P.natDegree := by
  change (P.comp (Polynomial.C h*Polynomial.X+Polynomial.C q)).natDegree=P.natDegree
  rw [Polynomial.natDegree_comp,Polynomial.natDegree_add_C,
    Polynomial.natDegree_C_mul_X h hh,mul_one]

theorem targetPolynomial_ne_zero (P : Polynomial R) (n : ℕ) (h q : R)
    (hP : P≠0) (hn : P.natDegree ≤ n) (hh : h≠0) : targetPolynomial P n h q≠0 := by
  intro hz
  have he := inverseSubstitution_target P n h q hn
  rw [hz,map_zero] at he
  exact mul_ne_zero (pow_ne_zero n (Polynomial.C_ne_zero.mpr hh)) hP he.symm

/-- Any common prime of the two cleared polynomials divides the
denominator itself. No coprimality of the cleared cuts is assumed. -/
theorem common_prime_dvd_denominator (P Q : Polynomial R) (n m : ℕ) (h q : R)
    (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m) (hh : h≠0)
    (hrel : IsRelPrime P Q) (D : Polynomial R) (hD : Prime D)
    (hDP : D ∣ targetPolynomial P n h q)
    (hDQ : D ∣ targetPolynomial Q m h q) : D ∣ Polynomial.C h := by
  by_contra hnot
  have hp := map_dvd (inverseSubstitution h q) hDP
  have hq := map_dvd (inverseSubstitution h q) hDQ
  rw [inverseSubstitution_target P n h q hn] at hp
  rw [inverseSubstitution_target Q m h q hm] at hq
  have hp' : inverseSubstitution h q D ∣ (Polynomial.C h)^(n+m)*P := by
    apply hp.trans
    refine ⟨(Polynomial.C h)^m,?_⟩
    rw [pow_add]; ring
  have hq' : inverseSubstitution h q D ∣ (Polynomial.C h)^(n+m)*Q := by
    apply hq.trans
    refine ⟨(Polynomial.C h)^n,?_⟩
    rw [pow_add]; ring
  have hscalar := common_dvd_scalar ((Polynomial.C h)^(n+m)) P Q
    (inverseSubstitution h q D) hrel hp' hq'
  have hdegree := Polynomial.natDegree_le_of_dvd hscalar
    (pow_ne_zero (n+m) (Polynomial.C_ne_zero.mpr hh))
  rw [inverseSubstitution_degree D h q hh] at hdegree
  have hdegree0 : D.natDegree=0 := by
    simpa using Nat.eq_zero_of_le_zero (by simpa using hdegree)
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hdegree0
  have hinverse : inverseSubstitution h q D=D := by
    rw [hconstant,inverseSubstitution_C]
  rw [hinverse] at hp hq
  have hnp : ¬ D ∣ (Polynomial.C h)^n := fun hpow => hnot (hD.dvd_of_dvd_pow hpow)
  have hnq : ¬ D ∣ (Polynomial.C h)^m := fun hpow => hnot (hD.dvd_of_dvd_pow hpow)
  have hdP : D ∣ P := (hD.dvd_or_dvd hp).resolve_left hnp
  have hdQ : D ∣ Q := (hD.dvd_or_dvd hq).resolve_left hnq
  exact hD.irreducible.not_isUnit (hrel hdP hdQ)

end Polynomial

#print axioms targetPolynomial_ne_zero
#print axioms common_prime_dvd_denominator
end
end ProximityPrize.SubmissionLower.MovingSourceProperness6814
