import ProximityPrize.Benchmark.TargetLower







/-!
# Actual local valuation bounds for a coordinate box

Model label: gpt-5.

The multiplicative bound below is derived from the actual monomial expansion
of a multivariate polynomial and the ultrametric finite-sum inequality for an
actual valuation. No polynomial height bound is supplied as a hypothesis.

The integer specialization uses the nonnegative pole order max(0, log(v(x))).
Its finite weighted-sum corollary applies to any already chosen finite family
of actual valuations. It does not construct curve places, a product formula,
a global pole divisor, or a geometric point-count bound.
-/

namespace ProximityPrize.SubmissionLower.ContactLocalPoleBound

open scoped BigOperators

noncomputable section

section Multiplicative

variable {K L σ Γ₀ : Type*} [Field K] [Field L] [Fintype σ]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- Actual evaluation of one monomial is bounded by its coordinate box. -/
theorem valuation_monomial_le (v : Valuation L Γ₀) (coeff : K →+* L)
    (hcoeff : ∀ c : K, v (coeff c) ≤ 1) (x : σ → L)
    (cap : σ → ℕ) (d : σ →₀ ℕ) (c : K) (hd : ∀ i, d i ≤ cap i) :
    v (MvPolynomial.eval₂Hom coeff x (MvPolynomial.monomial d c)) ≤
      ∏ i, max 1 (v (x i)) ^ cap i := by
  classical
  rw [MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_mul, map_prod]
  simp only [map_pow]
  calc
    v (coeff c) * (∏ i, v (x i) ^ d i) ≤
        1 * (∏ i, max 1 (v (x i)) ^ cap i) := by
      apply mul_le_mul' (hcoeff c)
      apply Finset.prod_le_prod (fun _ _ => zero_le)
      intro i _
      exact (pow_le_pow_left₀ zero_le (le_max_right _ _) (d i)).trans
        (pow_le_pow_right₀ (le_max_left _ _) (hd i))
    _ = _ := one_mul _

/-- The coordinate-box majorant follows from the polynomial itself. -/
theorem valuation_eval_le_box (v : Valuation L Γ₀) (coeff : K →+* L)
    (hcoeff : ∀ c : K, v (coeff c) ≤ 1) (x : σ → L)
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i) :
    v (MvPolynomial.eval₂Hom coeff x F) ≤
      ∏ i, max 1 (v (x i)) ^ cap i := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum F, map_sum]
  apply v.map_sum_le
  intro d hd
  apply valuation_monomial_le v coeff hcoeff x cap d
  intro i
  exact (MvPolynomial.monomial_le_degreeOf i hd).trans (hcap i)

/-- Including one on the left handles zero evaluations without logarithm
exceptions and retains the same actual coordinate majorant. -/
theorem max_one_valuation_eval_le_box (v : Valuation L Γ₀) (coeff : K →+* L)
    (hcoeff : ∀ c : K, v (coeff c) ≤ 1) (x : σ → L)
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i) :
    max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≤
      ∏ i, max 1 (v (x i)) ^ cap i := by
  classical
  apply max_le
  · exact Finset.one_le_prod fun _ _ => one_le_pow₀ (le_max_left _ _)
  · exact valuation_eval_le_box v coeff hcoeff x cap F hcap

end Multiplicative

section IntegerPole

variable {K L σ : Type*} [Field K] [Field L] [Fintype σ]

/-- Nonnegative integer pole order, including the zero-value convention. -/
def poleOrder (v : Valuation L (WithZero (Multiplicative ℤ))) (x : L) : ℤ :=
  max 0 (v x).log

/-- The zero convention for WithZero.log causes no issue after taking max 1. -/
theorem log_max_one (z : WithZero (Multiplicative ℤ)) :
    (max 1 z).log = max 0 z.log := by
  by_cases hz : z = 0
  · simp [hz]
  rcases le_total 1 z with h | h
  · have hlog : (0 : ℤ) ≤ z.log := by
      simpa using (WithZero.log_le_log (by simp) hz).2 h
    simp only [max_eq_right h, max_eq_right hlog]
  · have hlog : z.log ≤ (0 : ℤ) := by
      simpa using (WithZero.log_le_log hz (by simp)).2 h
    simp only [max_eq_left h, WithZero.log_one, max_eq_left hlog]

/-- Logarithm of an actual finite product whose factors are at least one. -/
theorem log_prod_of_one_le {ι : Type*} (s : Finset ι)
    (f : ι → WithZero (Multiplicative ℤ)) :
    (∀ i ∈ s, 1 ≤ f i) →
      (∏ i ∈ s, f i).log = ∑ i ∈ s, (f i).log := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
      intro hf
      have hfi : 1 ≤ f i := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, 1 ≤ f j :=
        fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hfi0 : f i ≠ 0 := ne_of_gt (zero_lt_one.trans_le hfi)
      have hprod0 : (∏ j ∈ s, f j) ≠ 0 :=
        ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfs))
      rw [Finset.prod_insert hi, WithZero.log_mul hfi0 hprod0,
        Finset.sum_insert hi, ih hfs]

/-- Actual discrete-valuation pole order of a box-bounded polynomial. -/
theorem poleOrder_eval_le_box
    (v : Valuation L (WithZero (Multiplicative ℤ))) (coeff : K →+* L)
    (hcoeff : ∀ c : K, v (coeff c) ≤ 1) (x : σ → L)
    (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i) :
    poleOrder v (MvPolynomial.eval₂Hom coeff x F) ≤
      ∑ i, (cap i : ℤ) * poleOrder v (x i) := by
  classical
  have hfactor : ∀ i ∈ (Finset.univ : Finset σ),
      1 ≤ max 1 (v (x i)) ^ cap i :=
    fun _ _ => one_le_pow₀ (le_max_left _ _)
  have hleft0 : max 1 (v (MvPolynomial.eval₂Hom coeff x F)) ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))
  have hright0 : (∏ i, max 1 (v (x i)) ^ cap i) ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (Finset.one_le_prod hfactor))
  have hlog := (WithZero.log_le_log hleft0 hright0).2
    (max_one_valuation_eval_le_box v coeff hcoeff x cap F hcap)
  rw [log_prod_of_one_le Finset.univ _ hfactor] at hlog
  simpa only [WithZero.log_pow, log_max_one, nsmul_eq_mul, poleOrder] using hlog

/-- A finite weighted local-pole ledger, using actual valuations at every
summand. This is not a global product-formula or place-existence statement. -/
theorem weighted_poleOrder_eval_le_box {τ : Type*} (S : Finset τ)
    (weight : τ → ℕ) (v : τ → Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : K →+* L) (hcoeff : ∀ t ∈ S, ∀ c : K, v t (coeff c) ≤ 1)
    (x : σ → L) (cap : σ → ℕ) (F : MvPolynomial σ K)
    (hcap : ∀ i, F.degreeOf i ≤ cap i) :
    (∑ t ∈ S, (weight t : ℤ) * poleOrder (v t) (MvPolynomial.eval₂Hom coeff x F)) ≤
      ∑ i, (cap i : ℤ) * (∑ t ∈ S, (weight t : ℤ) * poleOrder (v t) (x i)) := by
  classical
  calc
    _ ≤ ∑ t ∈ S, (weight t : ℤ) *
        (∑ i, (cap i : ℤ) * poleOrder (v t) (x i)) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (poleOrder_eval_le_box (v t) coeff (hcoeff t ht) x cap F hcap)
        (Int.natCast_nonneg (weight t))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro t _
      ring

end IntegerPole

end


end ProximityPrize.SubmissionLower.ContactLocalPoleBound
