import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas

set_option autoImplicit false

namespace SplitCut.Rect
noncomputable section
open MvPolynomial
open scoped BigOperators

variable {σ F : Type*} [Field F]

def recordWeight (w : σ → ℕ) :
    MvPolynomial σ F →+* Polynomial (MvPolynomial σ F) :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun i => Polynomial.C (X i) * Polynomial.X^(w i))

theorem record_monomial (w : σ → ℕ) (m : σ →₀ ℕ) (c : F) :
    recordWeight w (monomial m c) = Polynomial.monomial (Finsupp.weight w m) (monomial m c) := by
  change (monomial m c).eval₂ _ _ = _
  rw [eval₂_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← map_pow, ← map_prod, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul]
  have hmono : C c * (∏ i ∈ m.support, (X i : MvPolynomial σ F)^m i) = monomial m c := by
    simpa only [Finsupp.prod] using (MvPolynomial.monomial_eq (s := m) (a := c)).symm
  rw [hmono, Polynomial.C_mul_X_pow_eq_monomial]
  simp [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.mul_comm]

theorem record_coeff (w : σ → ℕ) (f : MvPolynomial σ F) (n : ℕ) (m : σ →₀ ℕ) :
    ((recordWeight w f).coeff n).coeff m = if Finsupp.weight w m = n then f.coeff m else 0 := by
  classical
  have hf := f.support_sum_monomial_coeff
  conv_lhs => rw [← hf]
  simp only [map_sum, record_monomial, Polynomial.finsetSum_coeff, coeff_sum]
  by_cases hm : m ∈ f.support
  · rw [Finset.sum_eq_single_of_mem m hm]
    · split_ifs <;> simp [Polynomial.coeff_monomial, *]
    · intro i hi hne
      by_cases h : Finsupp.weight w i = n
      · simp [h, MvPolynomial.coeff_monomial, hne]
      · simp [Polynomial.coeff_monomial, h]
  · have hz : f.coeff m = 0 := notMem_support_iff.mp hm
    simp only [hz, ite_self]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hne : i ≠ m := fun h => hm (h ▸ hi)
    by_cases h : Finsupp.weight w i = n
    · simp [h, MvPolynomial.coeff_monomial, hne]
    · simp [Polynomial.coeff_monomial, h]

theorem record_degree (w : σ → ℕ) (f : MvPolynomial σ F) :
    (recordWeight w f).natDegree = f.weightedTotalDegree w := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    ext m
    rw [record_coeff]
    by_cases hm : m ∈ f.support
    · simp [ne_of_lt ((le_weightedTotalDegree w hm).trans_lt hn)]
    · simp [notMem_support_iff.mp hm]
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    by_contra! hbig
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt hbig
    have hh := congrArg (fun p : MvPolynomial σ F => p.coeff m) hz
    simp [record_coeff] at hh
    exact (mem_support_iff.mp hm) hh

theorem record_ne_zero (w : σ → ℕ) {f : MvPolynomial σ F} (hf : f ≠ 0) :
    recordWeight w f ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
  have hz := record_coeff w f (Finsupp.weight w m) m
  rw [h] at hz
  exact hm (by simpa using hz.symm)

theorem weighted_degree_mul (w : σ → ℕ) {f g : MvPolynomial σ F} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f*g).weightedTotalDegree w = f.weightedTotalDegree w + g.weightedTotalDegree w := by
  rw [← record_degree w (f*g), map_mul,
    Polynomial.natDegree_mul (record_ne_zero w hf) (record_ne_zero w hg), record_degree, record_degree]

#print axioms weighted_degree_mul
end
end SplitCut.Rect
