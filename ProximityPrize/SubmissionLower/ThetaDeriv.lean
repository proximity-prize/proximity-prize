import ProximityPrize.SubmissionLower.ThetaGap
import ArkLib.Data.MvPolynomial.WeightedOrder
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
A derivation whose values on the variables lose at most `c` units of weighted order loses at
most `c` units on every polynomial.
-/

namespace ThetaDeriv
open MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weight_sub_single (ω : σ → ℕ) (e : σ →₀ ℕ) (i : σ) (hi : i ∈ e.support) :
    (e - Finsupp.single i 1).weight ω + ω i = e.weight ω := by
  classical
  have hle : Finsupp.single i 1 ≤ e := by
    rw [Finsupp.le_def]
    intro j
    by_cases h : j = i
    · subst h
      simpa using Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    · simp [Finsupp.single_apply, Ne.symm h]
  have h1 : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  have h2 := congrArg (Finsupp.weight ω) h1
  rw [map_add] at h2
  simpa [Finsupp.weight_apply, Finsupp.sum_single_index] using h2

theorem mkDerivation_mem_order (ω : σ → ℕ) (c : ℕ) (f : σ → MvPolynomial σ R)
    (hf : ∀ i, f i ∈ restrictWeightedOrder (R := R) ω (ω i - c)) {a : ℕ}
    {p : MvPolynomial σ R} (hp : p ∈ restrictWeightedOrder (R := R) ω a) :
    mkDerivation R f p ∈ restrictWeightedOrder (R := R) ω (a - c) := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  have hae : a ≤ e.weight ω := mem_restrictWeightedOrder.mp hp e he
  rw [mkDerivation_monomial]
  refine Submodule.smul_mem _ _ ?_
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [smul_eq_mul]
  have hw := weight_sub_single ω e i hi
  have hm : monomial (e - Finsupp.single i 1) ((e i : ℕ) : R) ∈
      restrictWeightedOrder (R := R) ω ((e - Finsupp.single i 1).weight ω) :=
    (monomial_mem_restrictWeightedOrder ω _ _ _).mpr (Or.inl le_rfl)
  exact restrictWeightedOrder_anti ω (by omega) (mul_mem_restrictWeightedOrder hm (hf i))

#print axioms mkDerivation_mem_order

/-- Polynomials all of whose monomials have weight at most `a`. -/
noncomputable def upper (ω : σ → ℕ) (a : ℤ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R {e | ((e.weight ω : ℕ) : ℤ) ≤ a}

theorem mem_upper {ω : σ → ℕ} {a : ℤ} {p : MvPolynomial σ R} :
    p ∈ upper (R := R) ω a ↔ ∀ e ∈ p.support, ((e.weight ω : ℕ) : ℤ) ≤ a :=
  Iff.rfl

theorem upper_mono (ω : σ → ℕ) {a b : ℤ} (h : a ≤ b) :
    upper (R := R) ω a ≤ upper (R := R) ω b :=
  fun _ hp e he => (mem_upper.mp hp e he).trans h

theorem monomial_mem_upper (ω : σ → ℕ) (e : σ →₀ ℕ) (r : R) {a : ℤ}
    (h : ((e.weight ω : ℕ) : ℤ) ≤ a) : monomial e r ∈ upper (R := R) ω a := by
  classical
  rw [mem_upper]
  intro e' he'
  have h' := support_monomial_subset he'
  rw [Finset.mem_singleton] at h'
  rw [h']
  exact h

theorem mul_mem_upper {ω : σ → ℕ} {a b : ℤ} {p q : MvPolynomial σ R}
    (hp : p ∈ upper (R := R) ω a) (hq : q ∈ upper (R := R) ω b) :
    p * q ∈ upper (R := R) ω (a + b) := by
  classical
  rw [mem_upper]
  intro e he
  obtain ⟨e1, h1, e2, h2, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
  have ha := mem_upper.mp hp e1 h1
  have hb := mem_upper.mp hq e2 h2
  rw [map_add]
  push_cast
  omega

/-- A derivation whose values on the variables drop the weight by at least `c` drops every
upper bound by `c`. -/
theorem mkDerivation_mem_upper (ω : σ → ℕ) (c : ℤ) (f : σ → MvPolynomial σ R)
    (hf : ∀ i, f i ∈ upper (R := R) ω ((ω i : ℤ) - c)) {a : ℤ}
    {p : MvPolynomial σ R} (hp : p ∈ upper (R := R) ω a) :
    mkDerivation R f p ∈ upper (R := R) ω (a - c) := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  have hae : ((e.weight ω : ℕ) : ℤ) ≤ a := mem_upper.mp hp e he
  rw [mkDerivation_monomial]
  refine Submodule.smul_mem _ _ ?_
  rw [Finsupp.sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [smul_eq_mul]
  have hw := weight_sub_single ω e i hi
  have hm : monomial (e - Finsupp.single i 1) ((e i : ℕ) : R) ∈
      upper (R := R) ω (((e - Finsupp.single i 1).weight ω : ℕ) : ℤ) :=
    monomial_mem_upper ω _ _ le_rfl
  exact upper_mono ω (by omega) (mul_mem_upper hm (hf i))

#print axioms mkDerivation_mem_upper

end ThetaDeriv
