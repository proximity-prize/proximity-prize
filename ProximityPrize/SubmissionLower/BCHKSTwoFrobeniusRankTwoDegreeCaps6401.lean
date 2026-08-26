import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusSymbolicKernel6401

/-!
# Exact degree caps for the two-Frobenius rank-two branch

This file derives the support bounds of the rectangular coefficient map
directly from its finite monomial expansion.  In particular, evaluation in
the outer variable cannot increase the inner `Z` support.  The final theorem
instantiates these generic bounds at the score-64.01 rectangle and proves the
advertised coordinate-mismatch degree cap.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusRankTwoDegreeCaps6401

open Polynomial
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusSymbolicKernel6401

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-- A rectangular coefficient box has no outer monomial at or beyond its
declared `X` depth. -/
theorem boxPolynomialMap_natDegree_le {F : Type*} [Field F]
    (xDepth zDepth : ℕ) (c : Fin xDepth × Fin zDepth → F) :
    (boxPolynomialMap xDepth zDepth c).natDegree ≤ xDepth - 1 := by
  classical
  rw [boxPolynomialMap_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q _hq
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_monomial_le _).trans
      (Nat.le_sub_one_of_lt q.1.isLt))

/-- Evaluation in the outer variable preserves the inner support bound of a
rectangular coefficient box. -/
theorem evalOuterAt_boxPolynomialMap_natDegree_le
    {F : Type*} [Field F] (x : F)
    (xDepth zDepth : ℕ) (c : Fin xDepth × Fin zDepth → F) :
    (evalOuterAt x (boxPolynomialMap xDepth zDepth c)).natDegree ≤
      zDepth - 1 := by
  classical
  rw [boxPolynomialMap_eq_sum]
  rw [show evalOuterAt x
      (∑ q : Fin xDepth × Fin zDepth,
        c q • Polynomial.monomial (q.1 : ℕ)
          (Polynomial.monomial (q.2 : ℕ) 1)) =
      ∑ q : Fin xDepth × Fin zDepth,
        evalOuterAt x
          (c q • Polynomial.monomial (q.1 : ℕ)
            (Polynomial.monomial (q.2 : ℕ) 1)) by
        simp [evalOuterAt, Polynomial.eval_finsetSum]]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q _hq
  simp only [evalOuterAt, Polynomial.eval_smul, Polynomial.eval_monomial]
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  calc
    (Polynomial.monomial (q.2 : ℕ) (1 : F) *
        Polynomial.C x ^ (q.1 : ℕ)).natDegree ≤
        (Polynomial.monomial (q.2 : ℕ) (1 : F)).natDegree +
          (Polynomial.C x ^ (q.1 : ℕ)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (zDepth - 1) + 0 := Nat.add_le_add
      ((Polynomial.natDegree_monomial_le _).trans
        (Nat.le_sub_one_of_lt q.2.isLt)) (by simp)
    _ = zDepth - 1 := Nat.add_zero _

/-- Swapping the two variables makes the global `Z` support of a
rectangular box its ordinary outer degree. -/
theorem swap_boxPolynomialMap_natDegree_le
    {F : Type*} [Field F]
    (xDepth zDepth : ℕ) (c : Fin xDepth × Fin zDepth → F) :
    (Polynomial.Bivariate.swap
      (boxPolynomialMap xDepth zDepth c)).natDegree ≤ zDepth - 1 := by
  classical
  rw [boxPolynomialMap_eq_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q _hq
  rw [map_smul, Polynomial.Bivariate.swap_monomial_monomial]
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_monomial_le _).trans
      (Nat.le_sub_one_of_lt q.2.isLt))

/-- Evaluating the outer variable is coefficientwise evaluation after
swapping the two variables, and hence cannot exceed the swapped degree. -/
theorem evalOuterAt_natDegree_le_swap_natDegree
    {F : Type*} [Field F] (x : F) (P : XOverZ F) :
    (evalOuterAt x P).natDegree ≤
      (Polynomial.Bivariate.swap P).natDegree := by
  rw [show evalOuterAt x P =
      (Polynomial.Bivariate.swap P).map (Polynomial.evalRingHom x) by
    unfold evalOuterAt
    simpa [Polynomial.aeval_def] using
      (Polynomial.Bivariate.aveal_eq_map_swap (R := F) x P)]
  exact Polynomial.natDegree_map_le

/-- Exact outer-`X` cap of the selected `(A₁,A₂)` minor. -/
theorem coefficientRowMap_denominator_outer_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F) :
    (symbolicRankTwoDenominator (coefficientRowMap c)
      (coefficientRowMap d)).natDegree ≤ 87382 := by
  have hc1 : ((coefficientRowMap c) 1).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a1XSlots6401] using
      (boxPolynomialMap_natDegree_le a1XSlots6401
        symbolicDepthOne6401 c.2.1)
  have hd1 : ((coefficientRowMap d) 1).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a1XSlots6401] using
      (boxPolynomialMap_natDegree_le a1XSlots6401
        symbolicDepthOne6401 d.2.1)
  have hc2 : ((coefficientRowMap c) 2).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a2XSlots6401] using
      (boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 c.2.2)
  have hd2 : ((coefficientRowMap d) 2).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a2XSlots6401] using
      (boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 d.2.2)
  unfold symbolicRankTwoDenominator
  exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc1 hd2))
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd1 hc2))

/-- Global (swapped-variable) `Z`-degree cap of the selected `(A₁,A₂)`
minor.  This is stronger than the pointwise evaluation cap and is stable
under cancellation of any nonzero polynomial factor. -/
theorem swap_coefficientRowMap_denominator_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F) :
    (Polynomial.Bivariate.swap
      (symbolicRankTwoDenominator (coefficientRowMap c)
        (coefficientRowMap d))).natDegree ≤ rankTwoDenomZCap6401 := by
  have hc1 :
      (Polynomial.Bivariate.swap ((coefficientRowMap c) 1)).natDegree ≤
        symbolicDepthOne6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a1XSlots6401
        symbolicDepthOne6401 c.2.1)
  have hd1 :
      (Polynomial.Bivariate.swap ((coefficientRowMap d) 1)).natDegree ≤
        symbolicDepthOne6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a1XSlots6401
        symbolicDepthOne6401 d.2.1)
  have hc2 :
      (Polynomial.Bivariate.swap ((coefficientRowMap c) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 c.2.2)
  have hd2 :
      (Polynomial.Bivariate.swap ((coefficientRowMap d) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 d.2.2)
  rw [symbolicRankTwoDenominator, map_sub, map_mul, map_mul]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc1 hd2) |>.trans
      (by
        norm_num [symbolicDepthOne6401, symbolicDepthFrobenius6401,
          rankTwoDenomZCap6401, balancedDepth6401, balancedThreshold6401,
          moduleIndexSum6401, a1XSlots6401, q6401])
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd1 hc2) |>.trans
      (by
        norm_num [symbolicDepthOne6401, symbolicDepthFrobenius6401,
          rankTwoDenomZCap6401, balancedDepth6401, balancedThreshold6401,
          moduleIndexSum6401, a1XSlots6401, q6401])

/-- Exact outer-`X` cap of the selected `(A₀,A₂)` numerator. -/
theorem coefficientRowMap_numerator_outer_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F) :
    (symbolicRankTwoNumerator (coefficientRowMap c)
      (coefficientRowMap d)).natDegree ≤ 218453 := by
  have hc0 : ((coefficientRowMap c) 0).natDegree ≤ 174762 := by
    simpa [coefficientRowMap, a0XSlots6401] using
      (boxPolynomialMap_natDegree_le a0XSlots6401 symbolicDepth6401 c.1)
  have hd0 : ((coefficientRowMap d) 0).natDegree ≤ 174762 := by
    simpa [coefficientRowMap, a0XSlots6401] using
      (boxPolynomialMap_natDegree_le a0XSlots6401 symbolicDepth6401 d.1)
  have hc2 : ((coefficientRowMap c) 2).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a2XSlots6401] using
      (boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 c.2.2)
  have hd2 : ((coefficientRowMap d) 2).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a2XSlots6401] using
      (boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 d.2.2)
  unfold symbolicRankTwoNumerator
  exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc0 hd2))
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd0 hc2))

/-- Global (swapped-variable) `Z`-degree cap of the selected `(A₀,A₂)`
minor. -/
theorem swap_coefficientRowMap_numerator_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F) :
    (Polynomial.Bivariate.swap
      (symbolicRankTwoNumerator (coefficientRowMap c)
        (coefficientRowMap d))).natDegree ≤ rankTwoMismatchZCap6401 := by
  have hc0 :
      (Polynomial.Bivariate.swap ((coefficientRowMap c) 0)).natDegree ≤
        symbolicDepth6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a0XSlots6401
        symbolicDepth6401 c.1)
  have hd0 :
      (Polynomial.Bivariate.swap ((coefficientRowMap d) 0)).natDegree ≤
        symbolicDepth6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a0XSlots6401
        symbolicDepth6401 d.1)
  have hc2 :
      (Polynomial.Bivariate.swap ((coefficientRowMap c) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 c.2.2)
  have hd2 :
      (Polynomial.Bivariate.swap ((coefficientRowMap d) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (swap_boxPolynomialMap_natDegree_le a2XSlots6401
        symbolicDepthFrobenius6401 d.2.2)
  rw [symbolicRankTwoNumerator, map_sub, map_mul, map_mul]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc0 hd2) |>.trans
      (by
        norm_num [symbolicDepth6401, symbolicDepthFrobenius6401,
          rankTwoMismatchZCap6401, balancedDepth6401,
          balancedThreshold6401, moduleIndexSum6401, a1XSlots6401,
          q6401])
  · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd0 hc2) |>.trans
      (by
        norm_num [symbolicDepth6401, symbolicDepthFrobenius6401,
          rankTwoMismatchZCap6401, balancedDepth6401,
          balancedThreshold6401, moduleIndexSum6401, a1XSlots6401,
          q6401])

/-- Each specialization of the selected `(A₁,A₂)` minor has the exact
rank-two denominator cap from the numerical audit. -/
theorem evaluated_coefficientRowMap_denominator_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F) (x : F) :
    (evalOuterAt x
      (symbolicRankTwoDenominator (coefficientRowMap c)
        (coefficientRowMap d))).natDegree ≤ rankTwoDenomZCap6401 := by
  have hc1 :
      (evalOuterAt x ((coefficientRowMap c) 1)).natDegree ≤
        symbolicDepthOne6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a1XSlots6401 symbolicDepthOne6401 c.2.1)
  have hd1 :
      (evalOuterAt x ((coefficientRowMap d) 1)).natDegree ≤
        symbolicDepthOne6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a1XSlots6401 symbolicDepthOne6401 d.2.1)
  have hc2 :
      (evalOuterAt x ((coefficientRowMap c) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a2XSlots6401 symbolicDepthFrobenius6401 c.2.2)
  have hd2 :
      (evalOuterAt x ((coefficientRowMap d) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a2XSlots6401 symbolicDepthFrobenius6401 d.2.2)
  calc
    (evalOuterAt x
      (symbolicRankTwoDenominator (coefficientRowMap c)
        (coefficientRowMap d))).natDegree =
        (evalOuterAt x ((coefficientRowMap c) 1) *
            evalOuterAt x ((coefficientRowMap d) 2) -
          evalOuterAt x ((coefficientRowMap d) 1) *
            evalOuterAt x ((coefficientRowMap c) 2)).natDegree := by
      simp [symbolicRankTwoDenominator, evalOuterAt]
    _ ≤ (symbolicDepthOne6401 - 1) +
          (symbolicDepthFrobenius6401 - 1) := by
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc1 hd2)
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd1 hc2)
    _ = rankTwoDenomZCap6401 := by
      norm_num [symbolicDepthOne6401, symbolicDepthFrobenius6401,
        rankTwoDenomZCap6401, balancedDepth6401, balancedThreshold6401,
        moduleIndexSum6401, a1XSlots6401, q6401]

/-- Each specialization of the selected `(A₀,A₂)` minor has the exact
rank-two numerator cap. -/
theorem evaluated_coefficientRowMap_numerator_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F) (x : F) :
    (evalOuterAt x
      (symbolicRankTwoNumerator (coefficientRowMap c)
        (coefficientRowMap d))).natDegree ≤ rankTwoMismatchZCap6401 := by
  have hc0 :
      (evalOuterAt x ((coefficientRowMap c) 0)).natDegree ≤
        symbolicDepth6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a0XSlots6401 symbolicDepth6401 c.1)
  have hd0 :
      (evalOuterAt x ((coefficientRowMap d) 0)).natDegree ≤
        symbolicDepth6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a0XSlots6401 symbolicDepth6401 d.1)
  have hc2 :
      (evalOuterAt x ((coefficientRowMap c) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a2XSlots6401 symbolicDepthFrobenius6401 c.2.2)
  have hd2 :
      (evalOuterAt x ((coefficientRowMap d) 2)).natDegree ≤
        symbolicDepthFrobenius6401 - 1 := by
    simpa [coefficientRowMap] using
      (evalOuterAt_boxPolynomialMap_natDegree_le x
        a2XSlots6401 symbolicDepthFrobenius6401 d.2.2)
  calc
    (evalOuterAt x
      (symbolicRankTwoNumerator (coefficientRowMap c)
        (coefficientRowMap d))).natDegree =
        (evalOuterAt x ((coefficientRowMap c) 0) *
            evalOuterAt x ((coefficientRowMap d) 2) -
          evalOuterAt x ((coefficientRowMap d) 0) *
            evalOuterAt x ((coefficientRowMap c) 2)).natDegree := by
      simp [symbolicRankTwoNumerator, evalOuterAt]
    _ ≤ (symbolicDepth6401 - 1) +
          (symbolicDepthFrobenius6401 - 1) := by
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc0 hd2)
      · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd0 hc2)
    _ = rankTwoMismatchZCap6401 := by
      norm_num [symbolicDepth6401, symbolicDepthFrobenius6401,
        rankTwoMismatchZCap6401, balancedDepth6401, balancedThreshold6401,
        moduleIndexSum6401, a1XSlots6401, q6401]

/-- The affine received coordinate has `Z` degree at most one, including all
degenerate choices of its two coefficients. -/
theorem affineValuePolynomial_natDegree_le_one {F : Type*} [Field F]
    (u₀ u₁ : F) : (affineValuePolynomial u₀ u₁).natDegree ≤ 1 := by
  unfold affineValuePolynomial
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

/-- Exact unconditional `Z`-degree ledger for every coordinate mismatch
arising from two rows in the balanced score-64.01 coefficient box. -/
theorem coordinateMismatch_coefficientRowMap_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F)
    (x u₀ u₁ : F) :
    (coordinateMismatch (coefficientRowMap c) (coefficientRowMap d)
      x u₀ u₁).natDegree ≤ rankTwoMismatchZCap6401 := by
  have hden := evaluated_coefficientRowMap_denominator_natDegree_le c d x
  have hnum := evaluated_coefficientRowMap_numerator_natDegree_le c d x
  unfold coordinateMismatch
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · apply Polynomial.natDegree_mul_le.trans
    calc
      (evalOuterAt x
          (symbolicRankTwoDenominator (coefficientRowMap c)
            (coefficientRowMap d))).natDegree +
          (affineValuePolynomial u₀ u₁).natDegree ≤
          rankTwoDenomZCap6401 + 1 :=
        Nat.add_le_add hden (affineValuePolynomial_natDegree_le_one u₀ u₁)
      _ = rankTwoMismatchZCap6401 := by
        norm_num [rankTwoDenomZCap6401, rankTwoMismatchZCap6401,
          balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
          a1XSlots6401, q6401]
  · exact hnum

end BCHKSTwoFrobeniusRankTwoDegreeCaps6401
end ProximityPrize.SubmissionLower
