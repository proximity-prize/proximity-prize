import ProximityPrize.SubmissionBinaryLower.P64Algebra

/-!
# Shared polynomial foundations: orders of bivariates, inverses modulo `X ^ s`

Bivariates are `Polynomial (Polynomial K)` with the outer variable `V` and the inner variable `U`
(the line coordinates of `P64LineOrder.lineShift`, with `K = F[Z]` or its fraction field).

* `OrdAtLeast k f`: every coefficient of `U^a V^b` with `a + b < k` vanishes.
  `ordAtLeast_mul` is the superadditivity of the order over any commutative semiring (the
  additive version over a domain is `P64LineOrder.tord_mul`).
* `mono a b = U^a V^b`, `coeff_mono`.
* `exists_mul_sub_one_X_pow_dvd`: a polynomial with unit constant term is a unit modulo `X ^ s`
  (Newton iteration).
* `exists_eq_lift_add_U_mul`: `f = f(0, V) + U·f₁`.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace P64Found

open Polynomial

section Order

variable {K : Type*} [CommSemiring K]

/-- The order (least total degree of a monomial `U^a V^b`) of `f` is at least `k`. -/
def OrdAtLeast (k : ℕ) (f : Polynomial (Polynomial K)) : Prop :=
  ∀ a b, a + b < k → (f.coeff b).coeff a = 0

lemma ordAtLeast_zero_left (f : Polynomial (Polynomial K)) : OrdAtLeast 0 f :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

lemma ordAtLeast_zero_right (k : ℕ) : OrdAtLeast k (0 : Polynomial (Polynomial K)) := by
  intro a b _
  simp

lemma OrdAtLeast.mono {k l : ℕ} {f : Polynomial (Polynomial K)} (h : OrdAtLeast k f)
    (hlk : l ≤ k) : OrdAtLeast l f :=
  fun a b hab => h a b (by omega)

lemma OrdAtLeast.add {k : ℕ} {f g : Polynomial (Polynomial K)} (hf : OrdAtLeast k f)
    (hg : OrdAtLeast k g) : OrdAtLeast k (f + g) := by
  intro a b hab
  simp [hf a b hab, hg a b hab]

/-- Superadditivity of the order. -/
theorem ordAtLeast_mul {k l : ℕ} {f g : Polynomial (Polynomial K)} (hf : OrdAtLeast k f)
    (hg : OrdAtLeast l g) : OrdAtLeast (k + l) (f * g) := by
  intro a b hab
  rw [coeff_mul, finsetSum_coeff]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun aa haa => ?_
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij haa
  by_cases h1 : aa.1 + ij.1 < k
  · rw [hf _ _ h1, zero_mul]
  · rw [hg _ _ (by omega), mul_zero]

/-- `U ^ s = C (X ^ s)` has order at least `s`. -/
lemma ordAtLeast_U_pow (s : ℕ) : OrdAtLeast s (C (X ^ s) : Polynomial (Polynomial K)) := by
  intro a b hab
  rw [coeff_C]
  split_ifs with hb
  · rw [coeff_X_pow]
    split_ifs <;> first | rfl | omega
  · rfl

/-- `V ^ s = X ^ s` has order at least `s`. -/
lemma ordAtLeast_V_pow (s : ℕ) : OrdAtLeast s (X ^ s : Polynomial (Polynomial K)) := by
  intro a b hab
  rw [coeff_X_pow]
  split_ifs with hb
  · subst hb
    rw [coeff_one]
    split_ifs <;> first | rfl | omega
  · rfl

/-- The monomial `U^a V^b`. -/
noncomputable def mono (a b : ℕ) : Polynomial (Polynomial K) := monomial b (monomial a 1)

lemma coeff_mono (a b a' b' : ℕ) :
    ((mono (K := K) a b).coeff b').coeff a' = if a = a' ∧ b = b' then 1 else 0 := by
  unfold mono
  rw [coeff_monomial]
  split_ifs with h1 h2 h2
  · rw [coeff_monomial]; simp [h2.1]
  · rw [coeff_monomial]
    exact if_neg (fun h => h2 ⟨h, h1⟩)
  · exact absurd h2.2 h1
  · rfl

lemma mono_eq (a b : ℕ) : (mono (K := K) a b) = C (X ^ a) * X ^ b := by
  unfold mono
  rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
  simp

end Order

section Inverse

variable {K : Type*} [CommRing K]

lemma newton_step {p w : K[X]} {s : ℕ} (h : X ^ s ∣ w * p - 1) :
    X ^ (2 * s) ∣ (w * (2 - w * p)) * p - 1 := by
  obtain ⟨q, hq⟩ := h
  refine ⟨-(q ^ 2), ?_⟩
  have : (w * (2 - w * p)) * p - 1 = -((w * p - 1) ^ 2) := by ring
  rw [this, hq]
  ring

/-- A polynomial with unit constant term is a unit modulo `X ^ s`. -/
theorem exists_mul_sub_one_X_pow_dvd {p : K[X]} (hp : IsUnit (p.coeff 0)) (s : ℕ) :
    ∃ w : K[X], X ^ s ∣ w * p - 1 := by
  obtain ⟨u, hu⟩ := hp
  have base : X ^ 1 ∣ C (↑u⁻¹ : K) * p - 1 := by
    rw [pow_one, X_dvd_iff, coeff_sub, coeff_C_mul, coeff_one_zero, ← hu]
    simp
  have key : ∀ k : ℕ, ∃ w : K[X], X ^ (2 ^ k) ∣ w * p - 1 := by
    intro k
    induction k with
    | zero => exact ⟨_, by simpa using base⟩
    | succ k ih =>
        obtain ⟨w, hw⟩ := ih
        refine ⟨w * (2 - w * p), ?_⟩
        rw [pow_succ, mul_comm]
        exact newton_step hw
  obtain ⟨w, hw⟩ := key s
  exact ⟨w, (pow_dvd_pow X (Nat.lt_two_pow_self).le).trans hw⟩

end Inverse

section Split

variable {K : Type*} [CommRing K]

/-- `f(0, V)` lifted back to a bivariate (constant in `U`). -/
noncomputable def atU0 (f : Polynomial (Polynomial K)) : Polynomial (Polynomial K) :=
  f.map ((C : K →+* K[X]).comp (constantCoeff (R := K)))

lemma coeff_atU0 (f : Polynomial (Polynomial K)) (b : ℕ) :
    (atU0 f).coeff b = C ((f.coeff b).coeff 0) := by
  simp [atU0, coeff_map]

/-- `f = f(0, V) + U·f₁`. -/
theorem exists_eq_atU0_add_U_mul (f : Polynomial (Polynomial K)) :
    ∃ f₁ : Polynomial (Polynomial K), f = atU0 f + C X * f₁ := by
  have hd : C X ∣ f - atU0 f := by
    rw [C_dvd_iff_dvd_coeff]
    intro i
    rw [coeff_sub, coeff_atU0]
    exact X_dvd_sub_C
  obtain ⟨f₁, hf₁⟩ := hd
  exact ⟨f₁, by rw [← hf₁]; ring⟩

end Split

end P64Found
end ProximityPrize.SubmissionBinaryLower
