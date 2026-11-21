import ProximityPrize.SubmissionLower.TwoFlag6929
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Division

set_option Elab.async false

/-!
O2 for the two-flag bound: `LcmDivisibility` holds for the four flag factors in `Form`.

* x₀, x₂ are primes (`MvPolynomial.X_prime`).
* quad = x₀x₁ − x₁² + x₀x₂ is linear in x₂ with coefficient x₀ and constant x₀x₁ − x₁².
  cubic = x₀²x₃ + x₀²x₂ − 2x₀x₁x₂ − x₀x₁² + x₁³ is linear in x₃ with coefficient x₀².
  After swapping that variable to position 0, `finSuccEquiv` turns each into `C c * X + C d`.
  The pair (d, c) is relatively prime (`IsRelPrime`: no common non-unit factor, NOT Bézout).
  So the linear polynomial is irreducible (`irreducible_of_degree_eq_one_of_isRelPrime_coeff`),
  hence prime in the UFD `MvPolynomial (Fin 4) Geom`.
* The six pairs are non-divisible (evaluation at explicit points).
* Prime powers with exponent max(v, w) each divide P, and are combined one prime at a time with
  `Prime.pow_dvd_of_dvd_mul_left`. Zero exponents are handled because `p ^ 0 = 1`.

Standalone module (not in the Solution closure), not built here.
-/

section PackSource_K1_13_1_1LcmFlag
set_option autoImplicit false
namespace K1_13_1_1

open K1_13
noncomputable section

/-- The quadratic test factor, literally as in `flagFactor`. -/
def quadForm : Form :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 1 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 2

/-- The cubic test factor, literally as in `flagFactor`. -/
def cubicForm : Form :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 3 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 -
    2 * MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 -
    MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 + MvPolynomial.X 1 ^ 3

theorem flagFactor_eq (v : FactorPowers) :
    flagFactor v = (MvPolynomial.X 0 : Form) ^ v.value * (MvPolynomial.X 2 : Form) ^ v.jetTwo *
      quadForm ^ v.quad * cubicForm ^ v.cubic := rfl

/-! ### Generic divisibility lemmas (any domain / UFD) -/

private theorem not_dvd_of_eval {n : ℕ} {p q : MvPolynomial (Fin n) Geom} (x : Fin n → Geom)
    (hp : MvPolynomial.eval x p = 0) (hq : MvPolynomial.eval x q ≠ 0) : ¬ p ∣ q := by
  rintro ⟨k, rfl⟩
  apply hq
  rw [map_mul, hp, zero_mul]

private theorem not_dvd_pow' {A : Type*} [CommRing A] [IsDomain A] {p q : A} (hp : Prime p)
    (h : ¬ p ∣ q) (n : ℕ) : ¬ p ∣ q ^ n :=
  fun h' => h (hp.dvd_of_dvd_pow h')

private theorem not_dvd_mul' {A : Type*} [CommRing A] [IsDomain A] {p a b : A} (hp : Prime p)
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b :=
  fun h => (hp.dvd_or_dvd h).elim ha hb

private theorem prime_pow_mul_dvd {A : Type*} [CommRing A] [IsDomain A] {p r y : A}
    (hp : Prime p) (hpr : ¬ p ∣ r) {m : ℕ} (h1 : p ^ m ∣ y) (h2 : r ∣ y) : p ^ m * r ∣ y := by
  obtain ⟨t, rfl⟩ := h2
  obtain ⟨u, rfl⟩ := hp.pow_dvd_of_dvd_mul_left m hpr h1
  exact ⟨u, by ring⟩

private theorem pow_max_dvd {A : Type*} [CommMonoid A] {x P : A} {a b : ℕ}
    (ha : x ^ a ∣ P) (hb : x ^ b ∣ P) : x ^ max a b ∣ P := by
  rcases le_total a b with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

/-- If `p` is prime and does not divide `d`, then `d` and `p ^ m` have no common non-unit factor. -/
private theorem isRelPrime_of_prime_pow {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {p d : A} (hp : Prime p) (hd : ¬ p ∣ d) (m : ℕ) :
    IsRelPrime d (p ^ m) := by
  intro r hrd hrp
  by_contra hu
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd (dvd_zero p)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hd0 (zero_dvd_iff.mp hrd)
  obtain ⟨q, hq, hqr⟩ := WfDvdMonoid.exists_irreducible_factor hu hr0
  have hqp : q ∣ p :=
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq).dvd_of_dvd_pow (hqr.trans hrp)
  obtain ⟨t, ht⟩ := hqp
  rcases hp.irreducible.isUnit_or_isUnit ht with h | h
  · exact hq.not_isUnit h
  · have hpq : p ∣ q := ⟨↑h.unit⁻¹, by rw [ht, mul_assoc, h.mul_val_inv, mul_one]⟩
    exact hd (hpq.trans (hqr.trans hrd))

/-- A form that becomes `C c * X + C d` (c ≠ 0, IsRelPrime d c) after a variable permutation
and `finSuccEquiv` is prime. -/
private theorem prime_of_linear_image (σ : Equiv.Perm (Fin 4)) (f : Form)
    (c d : MvPolynomial (Fin 3) Geom) (hc : c ≠ 0) (hrel : IsRelPrime d c)
    (hf : MvPolynomial.finSuccEquiv Geom 3 (MvPolynomial.rename σ f) =
      Polynomial.C c * Polynomial.X + Polynomial.C d) :
    Prime f := by
  have hp : Irreducible (Polynomial.C c * Polynomial.X + Polynomial.C d) :=
    Polynomial.irreducible_of_degree_eq_one_of_isRelPrime_coeff (Polynomial.degree_linear hc)
      (by simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hrel)
  have h1 : Irreducible (MvPolynomial.rename σ f) :=
    (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv Geom 3)
      (x := MvPolynomial.rename σ f)).mp (by rw [hf]; exact hp)
  have h2 : Irreducible f :=
    (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv Geom σ) (x := f)).mp
      (by rw [MvPolynomial.renameEquiv_apply]; exact h1)
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp h2

/-! ### The four factors -/

private theorem fse0 :
    MvPolynomial.finSuccEquiv Geom 3 (MvPolynomial.X 0 : Form) = Polynomial.X :=
  MvPolynomial.finSuccEquiv_X_zero

private theorem fse1 :
    MvPolynomial.finSuccEquiv Geom 3 (MvPolynomial.X 1 : Form) =
      Polynomial.C (MvPolynomial.X 0) :=
  MvPolynomial.finSuccEquiv_X_succ (j := 0)

private theorem fse2 :
    MvPolynomial.finSuccEquiv Geom 3 (MvPolynomial.X 2 : Form) =
      Polynomial.C (MvPolynomial.X 1) :=
  MvPolynomial.finSuccEquiv_X_succ (j := 1)

private theorem fse3 :
    MvPolynomial.finSuccEquiv Geom 3 (MvPolynomial.X 3 : Form) =
      Polynomial.C (MvPolynomial.X 2) :=
  MvPolynomial.finSuccEquiv_X_succ (j := 2)

private theorem quad_image :
    MvPolynomial.finSuccEquiv Geom 3 (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 2) quadForm) =
      Polynomial.C (MvPolynomial.X 1 : MvPolynomial (Fin 3) Geom) * Polynomial.X +
        Polynomial.C ((MvPolynomial.X 1 : MvPolynomial (Fin 3) Geom) * MvPolynomial.X 0 -
          MvPolynomial.X 0 ^ 2) := by
  have s0 : (Equiv.swap (0 : Fin 4) 2) 0 = 2 := by decide
  have s1 : (Equiv.swap (0 : Fin 4) 2) 1 = 1 := by decide
  have s2 : (Equiv.swap (0 : Fin 4) 2) 2 = 0 := by decide
  simp only [quadForm, map_add, map_sub, map_mul, map_pow, MvPolynomial.rename_X, s0, s1, s2,
    fse0, fse1, fse2]
  ring

private theorem cubic_image :
    MvPolynomial.finSuccEquiv Geom 3 (MvPolynomial.rename (Equiv.swap (0 : Fin 4) 3) cubicForm) =
      Polynomial.C ((MvPolynomial.X 2 : MvPolynomial (Fin 3) Geom) ^ 2) * Polynomial.X +
        Polynomial.C ((MvPolynomial.X 2 : MvPolynomial (Fin 3) Geom) ^ 2 * MvPolynomial.X 1 -
          2 * MvPolynomial.X 2 * MvPolynomial.X 0 * MvPolynomial.X 1 -
          MvPolynomial.X 2 * MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 ^ 3) := by
  have s0 : (Equiv.swap (0 : Fin 4) 3) 0 = 3 := by decide
  have s1 : (Equiv.swap (0 : Fin 4) 3) 1 = 1 := by decide
  have s2 : (Equiv.swap (0 : Fin 4) 3) 2 = 2 := by decide
  have s3 : (Equiv.swap (0 : Fin 4) 3) 3 = 0 := by decide
  simp only [cubicForm, map_add, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.rename_X,
    s0, s1, s2, s3, fse0, fse1, fse2, fse3]
  ring

theorem x0_prime : Prime (MvPolynomial.X 0 : Form) := MvPolynomial.X_prime
theorem x2_prime : Prime (MvPolynomial.X 2 : Form) := MvPolynomial.X_prime

theorem quadForm_prime : Prime quadForm := by
  have hnd : ¬ (MvPolynomial.X 1 : MvPolynomial (Fin 3) Geom) ∣
      MvPolynomial.X 1 * MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2 :=
    not_dvd_of_eval ![1, 0, 0] (by simp) (by simp)
  have hrel := isRelPrime_of_prime_pow MvPolynomial.X_prime hnd 1
  rw [pow_one] at hrel
  exact prime_of_linear_image _ _ _ _ (MvPolynomial.X_ne_zero 1) hrel quad_image

theorem cubicForm_prime : Prime cubicForm := by
  have hnd : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin 3) Geom) ∣
      MvPolynomial.X 2 ^ 2 * MvPolynomial.X 1 - 2 * MvPolynomial.X 2 * MvPolynomial.X 0 *
        MvPolynomial.X 1 - MvPolynomial.X 2 * MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 ^ 3 :=
    not_dvd_of_eval ![1, 0, 0] (by simp) (by simp)
  have hrel := isRelPrime_of_prime_pow MvPolynomial.X_prime hnd 2
  exact prime_of_linear_image _ _ _ _ (pow_ne_zero 2 (MvPolynomial.X_ne_zero 2)) hrel cubic_image

/-! ### Pairwise non-divisibility (explicit evaluation points) -/

theorem x0_not_dvd_x2 : ¬ (MvPolynomial.X 0 : Form) ∣ MvPolynomial.X 2 :=
  not_dvd_of_eval ![0, 0, 1, 0] (by simp) (by simp)

theorem x0_not_dvd_quad : ¬ (MvPolynomial.X 0 : Form) ∣ quadForm :=
  not_dvd_of_eval ![0, 1, 0, 0] (by simp) (by simp [quadForm])

theorem x0_not_dvd_cubic : ¬ (MvPolynomial.X 0 : Form) ∣ cubicForm :=
  not_dvd_of_eval ![0, 1, 0, 0] (by simp) (by simp [cubicForm])

theorem x2_not_dvd_quad : ¬ (MvPolynomial.X 2 : Form) ∣ quadForm :=
  not_dvd_of_eval ![0, 1, 0, 0] (by simp) (by simp [quadForm])

theorem x2_not_dvd_cubic : ¬ (MvPolynomial.X 2 : Form) ∣ cubicForm :=
  not_dvd_of_eval ![0, 1, 0, 0] (by simp) (by simp [cubicForm])

theorem quad_not_dvd_cubic : ¬ quadForm ∣ cubicForm :=
  not_dvd_of_eval ![1, 0, 0, 1] (by simp [quadForm]) (by simp [cubicForm])

/-! ### O2 -/

/-- O2 proved: divisibility by two flag factors gives divisibility by the componentwise-max flag. -/
theorem lcmDivisibility : LcmDivisibility := by
  intro v w P hv hw
  rw [flagFactor_eq] at hv hw
  show (MvPolynomial.X 0 : Form) ^ max v.value w.value *
      (MvPolynomial.X 2 : Form) ^ max v.jetTwo w.jetTwo *
      quadForm ^ max v.quad w.quad * cubicForm ^ max v.cubic w.cubic ∣ P
  have hC : cubicForm ^ max v.cubic w.cubic ∣ P :=
    pow_max_dvd ((dvd_mul_left _ _).trans hv) ((dvd_mul_left _ _).trans hw)
  have hQ : quadForm ^ max v.quad w.quad ∣ P :=
    pow_max_dvd ((dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hv)
      ((dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hw)
  have hX2 : (MvPolynomial.X 2 : Form) ^ max v.jetTwo w.jetTwo ∣ P :=
    pow_max_dvd ((dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _).trans hv)
      ((dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _).trans hw)
  have hX0 : (MvPolynomial.X 0 : Form) ^ max v.value w.value ∣ P :=
    pow_max_dvd ((dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _).trans hv)
      ((dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _).trans hw)
  have h2 := prime_pow_mul_dvd quadForm_prime
    (not_dvd_pow' quadForm_prime quad_not_dvd_cubic _) hQ hC
  have h3 := prime_pow_mul_dvd x2_prime
    (not_dvd_mul' x2_prime (not_dvd_pow' x2_prime x2_not_dvd_quad _)
      (not_dvd_pow' x2_prime x2_not_dvd_cubic _)) hX2 h2
  have h4 := prime_pow_mul_dvd x0_prime
    (not_dvd_mul' x0_prime (not_dvd_pow' x0_prime x0_not_dvd_x2 _)
      (not_dvd_mul' x0_prime (not_dvd_pow' x0_prime x0_not_dvd_quad _)
        (not_dvd_pow' x0_prime x0_not_dvd_cubic _))) hX0 h3
  simpa only [mul_assoc] using h4

/-- Two-flag block bound with O2 discharged; only O3 (`CofactorBand`) remains as a hypothesis. -/
theorem rank_block_le_twoFlag_of_cofactor (hC : CofactorBand) (s : ℕ) (g : ℤ)
    (v w : FactorPowers)
    (hv : v.degree ≤ residualDegree s ∧ v.maxIndex ≤ 48 ∧ v.maxTop ≤ 10)
    (hw : w.degree ≤ residualDegree s ∧ w.maxIndex ≤ 48 ∧ w.maxTop ≤ 10) :
    Module.finrank Geom (LinearMap.range (blockMap s g)) + (flagKernel s g v + flagKernel s g w) ≤
      bandCount (residualDegree s) (-g) 48 10 + lcmBand s g v w :=
  rank_block_le_twoFlag lcmDivisibility hC s g v w hv hw

end
end K1_13_1_1
end PackSource_K1_13_1_1LcmFlag
