import ProximityPrize.SubmissionLower.PoleFamily
import Mathlib.Algebra.MvPolynomial.Division

namespace PoleTruncation

open PoleBlocks PoleFamily MvPolynomial
open scoped BigOperators Matrix

noncomputable section

/-- Assemble the active chart polynomial for one fixed passive exponent. -/
def passivePolynomial {F : Type*} [Field F] {U B J : ℕ}
    (coeffs : Sigma (@Columns U B J) → F) (u : Fin (U+1)) : MvPolynomial (Fin 4) F :=
  ∑ c, if c.1.1 = u then C (coeffs c) * chartMonomial F (colInput c) else 0

theorem coeff_at_row {F : Type*} [Field F] {U B J : ℕ}
    (coeffs : Sigma (@Columns U B J) → F) (r : Sigma (@Rows U B J)) :
    (passivePolynomial coeffs r.1.1).coeff (rowExponent r) =
      (matrix F U B J).mulVec coeffs r := by
  rw [passivePolynomial, coeff_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases h : c.1.1 = r.1.1
  · simp [h, matrix, coeff_C_mul]
    exact mul_comm _ _
  · simp [h, Ne.symm h, matrix]

private theorem input_bounds {U B J : ℕ} (c : Sigma (@Columns U B J)) :
    (colInput c).b ≤ U-c.1.1.val ∧ (colInput c).q ≤ B ∧ (colInput c).j ≤ J := by
  have h := c.2.1.property
  have hq := c.2.1.val.isLt
  have hj := c.2.2.isLt
  change c.1.2.1.val - c.2.1.val.val ≤ U-c.1.1.val ∧
    c.2.1.val.val ≤ B ∧ (-(offset c.1)).toNat + c.2.2.val ≤ J
  unfold slotCount at hj
  omega

/-- A kernel vector has no low-X coefficient at any passive exponent. A
possible nonzero term automatically supplies the otherwise missing row. -/
theorem coeff_zero_of_mulVec_zero {F : Type*} [Field F] {U B J : ℕ}
    (coeffs : Sigma (@Columns U B J) → F)
    (hker : (matrix F U B J).mulVec coeffs = 0)
    (u : Fin (U+1)) (e : Fin 4 →₀ ℕ) (hx : e 0 < B+J) :
    (passivePolynomial coeffs u).coeff e = 0 := by
  classical
  by_cases hex : ∃ c : Sigma (@Columns U B J), c.1.1 = u ∧
      (chartMonomial F (colInput c)).coeff e ≠ 0
  · obtain ⟨c, hu, hc⟩ := hex
    obtain ⟨hb,hq,hj⟩ := input_bounds c
    have ha : (colInput c).a < B+J := by
      by_contra! h
      exact hc (coeff_zero_below_source_X _ _ (hx.trans_le h))
    obtain ⟨r,_,hr,_,hre,_,_⟩ :=
      coefficient_represented u (colInput c) e (hu ▸ hb) hq hj ha hx hc
    rw [← hre, ← hr, coeff_at_row coeffs r, hker]
    rfl
  · rw [passivePolynomial, coeff_sum]
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    by_cases hu : c.1.1 = u
    · have hc : (chartMonomial F (colInput c)).coeff e = 0 := by
        by_contra h
        exact hex ⟨c,hu,h⟩
      simp [hu, coeff_C_mul, hc]
    · simp [hu]

theorem X_pow_dvd_of_coeff_zero {F : Type*} [Field F] (p : MvPolynomial (Fin 4) F) (m : ℕ)
    (h : ∀ e : Fin 4 →₀ ℕ, e 0 < m → p.coeff e = 0) :
    X (0 : Fin 4)^m ∣ p := by
  classical
  conv_rhs => rw [p.as_sum]
  apply Finset.dvd_sum
  intro e he
  have hme : m ≤ e 0 := by
    by_contra! hh
    exact (mem_support_iff.mp he) (h e hh)
  rw [X_pow_eq_monomial, monomial_dvd_monomial]
  exact ⟨Or.inr (Finsupp.single_le_iff.mpr hme), one_dvd _⟩

/-- The normalized matrix kernel produces an X-adically divisible
polynomial in each passive seed degree. -/
theorem X_pow_dvd_passivePolynomial {F : Type*} [Field F] {U B J : ℕ}
    (coeffs : Sigma (@Columns U B J) → F)
    (hker : (matrix F U B J).mulVec coeffs = 0) (u : Fin (U+1)) :
    X (0 : Fin 4)^(B+J) ∣ passivePolynomial coeffs u :=
  X_pow_dvd_of_coeff_zero _ _ (fun e he ↦ coeff_zero_of_mulVec_zero coeffs hker u e he)

/-- The divisibility conditions, in turn, annihilate all rows of the matrix. -/
theorem mulVec_zero_iff_X_pow_dvd {F : Type*} [Field F] {U B J : ℕ}
    (coeffs : Sigma (@Columns U B J) → F) :
    (matrix F U B J).mulVec coeffs = 0 ↔
      ∀ u : Fin (U+1), X (0 : Fin 4)^(B+J) ∣ passivePolynomial coeffs u := by
  constructor
  · exact X_pow_dvd_passivePolynomial coeffs
  · intro h
    funext r
    change (matrix F U B J).mulVec coeffs r = 0
    rw [← coeff_at_row]
    have hx : rowExponent r 0 < B+J := by
      have hl := r.2.2.val.isLt
      have hp := r.2.2.property.2
      simp [rowExponent, blockOutput, exponent]
      omega
    obtain ⟨p,hp⟩ := h r.1.1
    rw [hp, X_pow_eq_monomial, coeff_monomial_mul', ite_eq_right]
    exact fun he ↦ (not_le_of_gt hx) (Finsupp.single_le_iff.mp he)

end
end PoleTruncation
