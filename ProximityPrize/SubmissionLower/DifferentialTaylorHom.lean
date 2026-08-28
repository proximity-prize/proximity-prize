import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.DifferentialTaylorCoefficients




/-!
# Finite algebraic Taylor homomorphism and the final-tail boundary

Model label: gpt-5.

The target is the actual quotient by `(X^bound)`. Multiplicativity comes
from the finite iterated Leibniz rule, not from an assumed homomorphism.
The derivative identity explicitly uses the coefficient at `bound`, which
is outside the displayed truncated polynomial. This is why the polynomiality
locus must impose its last tail as well as all earlier tails.

The low-degree identity finish below is purely algebraic. Rational numerator
degree bounds, localization, and the mixed geometric counting theorem are
separate obligations; this module does not claim an improving submission.
-/

namespace ProximityPrize.SubmissionLower.DifferentialTaylorHom

open DifferentialTaylorCoefficients

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

section TaylorMap

variable {K A L : Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]

noncomputable def truncationIdeal (L : Type*) [Field L] (bound : ℕ) : Ideal (Polynomial L) :=
  Ideal.span ({(Polynomial.X : Polynomial L) ^ bound} : Set (Polynomial L))

abbrev TruncatedPolynomials (L : Type*) [Field L] (bound : ℕ) :=
  Polynomial L ⧸ truncationIdeal L bound

noncomputable def taylorHom
    (D : Derivation K A A) (value : A →+* L) (bound : ℕ)
    (hbound : 0 < bound)
    (hfactorial : ∀ j < bound, (j.factorial : L) ≠ 0) :
    A →+* TruncatedPolynomials L bound where
  toFun a := Ideal.Quotient.mk (truncationIdeal L bound)
    (jetPolynomial D value bound a)
  map_zero' := by rw [jetPolynomial_zero, map_zero]
  map_one' := by rw [jetPolynomial_one D value bound hbound, map_one]
  map_add' a b := by rw [jetPolynomial_add, map_add]
  map_mul' a b := by
    rw [← map_mul]
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_singleton.mpr
    exact X_pow_dvd_jetPolynomial_product_error D value bound a b hfactorial

theorem taylorHom_apply
    (D : Derivation K A A) (value : A →+* L) (bound : ℕ)
    (hbound : 0 < bound)
    (hfactorial : ∀ j < bound, (j.factorial : L) ≠ 0) (a : A) :
    taylorHom D value bound hbound hfactorial a =
      Ideal.Quotient.mk (truncationIdeal L bound) (jetPolynomial D value bound a) :=
  rfl

theorem iterate_eq_zero_of_derivation_eq_zero
    (D : Derivation K A A) (a : A) (ha : D a = 0) (n : ℕ) (hn : n ≠ 0) :
    D^[n] a = 0 := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    rw [Function.iterate_succ_apply, ha]
    exact iterate_zero D n

theorem jetPolynomial_of_derivation_eq_zero
    (D : Derivation K A A) (value : A →+* L) (bound : ℕ)
    (hbound : 0 < bound) (a : A) (ha : D a = 0) :
    jetPolynomial D value bound a = Polynomial.C (value a) := by
  ext j
  by_cases hj : j = 0
  · subst j
    simp [jetPolynomial_coeff, jetCoefficient, hbound]
  · have hiter := iterate_eq_zero_of_derivation_eq_zero D a ha j hj
    simp [jetPolynomial_coeff, jetCoefficient, hiter, Polynomial.coeff_C, hj]

theorem jetPolynomial_algebraMap
    (D : Derivation K A A) (value : A →+* L) (bound : ℕ)
    (hbound : 0 < bound) (c : K) :
    jetPolynomial D value bound (algebraMap K A c) =
      Polynomial.C (value (algebraMap K A c)) :=
  jetPolynomial_of_derivation_eq_zero D value bound hbound _ (D.map_algebraMap c)

theorem jetCoefficient_derivation
    (D : Derivation K A A) (value : A →+* L) (a : A) (n : ℕ)
    (hn : (n.factorial : L) ≠ 0)
    (hsucc : ((n + 1).factorial : L) ≠ 0) :
    jetCoefficient D value (D a) n =
      jetCoefficient D value a (n + 1) * (n + 1 : L) := by
  have hcast : (n + 1 : L) ≠ 0 := by
    have hmul : (n + 1 : L) * (n.factorial : L) ≠ 0 := by
      simpa only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hsucc
    exact (mul_ne_zero_iff.mp hmul).1
  simp only [jetCoefficient, Function.iterate_succ_apply,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The coefficient at `bound`, not merely those below it, is necessary
to identify the truncated derivative with the derivative of the truncation. -/
theorem jetPolynomial_derivation_eq_derivative
    (D : Derivation K A A) (value : A →+* L) (bound : ℕ) (a : A)
    (hfactorial : ∀ j ≤ bound, (j.factorial : L) ≠ 0)
    (hlast : jetCoefficient D value a bound = 0) :
    jetPolynomial D value bound (D a) =
      (jetPolynomial D value bound a).derivative := by
  ext j
  rw [Polynomial.coeff_derivative, jetPolynomial_coeff, jetPolynomial_coeff]
  by_cases hj : j < bound
  · rw [if_pos hj, jetCoefficient_derivation D value a j
      (hfactorial j hj.le) (hfactorial (j + 1) (by omega))]
    by_cases hnext : j + 1 < bound
    · rw [if_pos hnext]
    · have heq : j + 1 = bound := by omega
      simp [heq, hlast]
  · have hnext : ¬j + 1 < bound := by omega
    rw [if_neg hj, if_neg hnext, zero_mul]

/-- The last-tail derivative identity in the safe positive-characteristic
range. In particular, no factorial of size `bound+1` is required. -/
theorem jetPolynomial_derivation_eq_derivative_of_char
    (D : Derivation K A A) (value : A →+* L) (p bound : ℕ) [CharP L p]
    (hbound : bound < p) (a : A)
    (hlast : jetCoefficient D value a bound = 0) :
    jetPolynomial D value bound (D a) =
      (jetPolynomial D value bound a).derivative := by
  apply jetPolynomial_derivation_eq_derivative D value bound a
  · intro j hj
    exact factorial_cast_ne_zero_below_characteristic p j (lt_of_le_of_lt hj hbound)
  · exact hlast

/-- The earlier tails really shorten the Taylor polynomial. The final tail
at `bound` is a separate condition, used in the derivative theorem above. -/
theorem jetPolynomial_eq_shorter_of_tails_zero
    (D : Derivation K A A) (value : A →+* L) (small bound : ℕ) (a : A)
    (hsmall : small ≤ bound)
    (htails : ∀ j, small ≤ j → j < bound → jetCoefficient D value a j = 0) :
    jetPolynomial D value bound a = jetPolynomial D value small a := by
  ext j
  rw [jetPolynomial_coeff, jetPolynomial_coeff]
  by_cases hj : j < small
  · rw [if_pos hj, if_pos (lt_of_lt_of_le hj hsmall)]
  · rw [if_neg hj]
    by_cases hb : j < bound
    · rw [if_pos hb, htails j (by omega) hb]
    · rw [if_neg hb]

/-- A polynomial of degree strictly below the truncation order is already
zero if its quotient class is zero. There is no formal-series assumption. -/
theorem eq_zero_of_quotient_eq_zero_of_natDegree_lt
    (bound : ℕ) (Q : Polynomial L) (hdegree : Q.natDegree < bound)
    (hzero : Ideal.Quotient.mk (truncationIdeal L bound) Q = 0) : Q = 0 := by
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hdvd : (Polynomial.X : Polynomial L) ^ bound ∣ Q :=
    Ideal.mem_span_singleton.mp hmem
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hdvd
  ext j
  rw [Polynomial.coeff_zero]
  by_cases hj : j < bound
  · exact hcoeff j hj
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdegree (by omega))

end TaylorMap

section PolynomialRelation

variable {K A L σ : Type*} [CommRing K] [CommRing A] [Algebra K A] [Field L]

/-- A concrete substitution diagram transports a genuine algebraic
relation through the constructed Taylor homomorphism. The degree condition
then upgrades the truncated identity to an exact polynomial identity. -/
theorem polynomial_relation_of_taylor_substitution
    (D : Derivation K A A) (value : A →+* L) (bound : ℕ)
    (hbound : 0 < bound)
    (hfactorial : ∀ j < bound, (j.factorial : L) ≠ 0)
    (coordinates : σ → A) (polynomials : σ → Polynomial L)
    (hcoordinates : ∀ i,
      jetPolynomial D value bound (coordinates i) = polynomials i)
    (F : MvPolynomial σ K)
    (hrelation : MvPolynomial.eval₂Hom (algebraMap K A) coordinates F = 0)
    (hdegree : (MvPolynomial.eval₂Hom
      (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F).natDegree < bound) :
    MvPolynomial.eval₂Hom
      (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F = 0 := by
  let τ := taylorHom D value bound hbound hfactorial
  let mk := Ideal.Quotient.mk (truncationIdeal L bound)
  have hhom : τ.comp (MvPolynomial.eval₂Hom (algebraMap K A) coordinates) =
      mk.comp (MvPolynomial.eval₂Hom
        (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      change mk (jetPolynomial D value bound (algebraMap K A c)) =
        mk (Polynomial.C (value (algebraMap K A c)))
      rw [jetPolynomial_algebraMap D value bound hbound]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      change mk (jetPolynomial D value bound (coordinates i)) = mk (polynomials i)
      rw [hcoordinates]
  apply eq_zero_of_quotient_eq_zero_of_natDegree_lt bound _ hdegree
  have hF := RingHom.congr_fun hhom F
  change τ (MvPolynomial.eval₂Hom (algebraMap K A) coordinates F) =
    mk (MvPolynomial.eval₂Hom
      (Polynomial.C.comp (value.comp (algebraMap K A))) polynomials F) at hF
  rw [hrelation, map_zero] at hF
  exact hF.symm

end PolynomialRelation

end ProximityPrize.SubmissionLower.DifferentialTaylorHom

#print axioms ProximityPrize.SubmissionLower.DifferentialTaylorHom.taylorHom
#print axioms ProximityPrize.SubmissionLower.DifferentialTaylorHom.jetPolynomial_derivation_eq_derivative
#print axioms ProximityPrize.SubmissionLower.DifferentialTaylorHom.jetPolynomial_derivation_eq_derivative_of_char
#print axioms ProximityPrize.SubmissionLower.DifferentialTaylorHom.polynomial_relation_of_taylor_substitution
