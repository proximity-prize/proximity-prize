import ProximityPrize.SubmissionLower.BCHKSPolynomialPairDeterminant6400

/-! # Algebra of a polynomial multiplier family -/

namespace ProximityPrize.SubmissionLower

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Eliminate the determinant wrapper without asking a concrete production
proof to normalize the underlying bounded-pair subtypes. -/
theorem polynomialPair_cross_eq_of_det_eq_zero
    {F : Type} [Field F] {c h : Nat}
    (u v : PolynomialPairSpace F c h)
    (hdet : polynomialPairDet u v = 0) :
    u.1.1 * v.2.1 = u.2.1 * v.1.1 := by
  exact sub_eq_zero.mp hdet

/-- Cancel a nonzero common factor from a rank-one cross relation, then use
coprimality of the primitive pair to obtain one polynomial multiplier for
both lanes. -/
theorem exists_multiplier_of_factored_coprime_cross
    {F : Type} [Field F]
    (H A B A₁ B₁ : F[X])
    (hH : H ≠ 0) (hB : B ≠ 0) (hcoprime : IsCoprime A B)
    (hcross : (H * A) * B₁ = (H * B) * A₁) :
    ∃ M : F[X], A₁ = M * A ∧ B₁ = M * B := by
  have hprimitiveCross : A * B₁ = B * A₁ := by
    apply mul_left_cancel₀ hH
    simpa only [mul_assoc] using hcross
  obtain ⟨M, hB₁, hA₁⟩ :=
    exists_polynomial_multiplier_of_coprime_cross
      B A B₁ A₁ hB hcoprime.symm hprimitiveCross.symm
  exact ⟨M, hA₁, hB₁⟩

/-- Linear independence of bounded polynomial pairs transfers to their
common polynomial multipliers. -/
theorem linearIndependent_multipliers_of_pair_factors
    {F J : Type} [Field F] [Fintype J]
    {c h : Nat}
    (pairFamily : J → PolynomialPairSpace F c h)
    (multipliers : J → F[X]) (A B : F[X])
    (hpairLI : LinearIndependent F pairFamily)
    (hA : ∀ j, (pairFamily j).1.1 = multipliers j * A)
    (hB : ∀ j, (pairFamily j).2.1 = multipliers j * B) :
    LinearIndependent F multipliers := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients hsum j
  apply (Fintype.linearIndependent_iff.mp hpairLI coefficients) ?_
  apply Prod.ext
  · apply Subtype.ext
    simp only [Prod.fst_sum, Prod.smul_fst, Prod.fst_zero,
      Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    change (∑ i, coefficients i • (pairFamily i).1.1) = 0
    calc
      (∑ i, coefficients i • (pairFamily i).1.1) =
          (∑ i, coefficients i • multipliers i) * A := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hA i]
            simp only [smul_eq_C_mul]
            ring
      _ = 0 := by rw [hsum, zero_mul]
  · apply Subtype.ext
    simp only [Prod.snd_sum, Prod.smul_snd, Prod.snd_zero,
      Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    change (∑ i, coefficients i • (pairFamily i).2.1) = 0
    calc
      (∑ i, coefficients i • (pairFamily i).2.1) =
          (∑ i, coefficients i • multipliers i) * B := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hB i]
            simp only [smul_eq_C_mul]
            ring
      _ = 0 := by rw [hsum, zero_mul]

/-- Exact degree subtraction through a nonzero primitive lane. -/
theorem multiplier_natDegree_lt_sub_of_factor
    {F : Type} [Field F]
    (M B Raw : F[X]) (t : Nat)
    (hM : M ≠ 0) (hB : B ≠ 0)
    (hfactor : Raw = M * B) (hRaw : Raw.natDegree < t) :
    M.natDegree < t - B.natDegree := by
  have hdegree := congrArg Polynomial.natDegree hfactor
  rw [Polynomial.natDegree_mul hM hB] at hdegree
  omega

end ProximityPrize.SubmissionLower
