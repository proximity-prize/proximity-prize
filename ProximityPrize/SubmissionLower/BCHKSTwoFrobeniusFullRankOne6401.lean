import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRankTwoClosure6401

/-!
# The projected two-Frobenius rank-one residual is full rank one

The rational rank-two closure leaves the case in which every `(A₁,A₂)`
minor of the balanced symbolic kernel vanishes.  This file records the
missing propagation to the two minors involving `A₀`.

At each of the `262144` locator coordinates, the two kernel relations and
the vanishing `(A₁,A₂)` minor force both remaining minors to vanish.  Their
outer `X` degree is at most `174762 + 43691 = 218453`, strictly less than
the number of distinct locators, so ordinary polynomial root counting over
the coefficient domain `F[Z]` makes them vanish identically.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusFullRankOne6401

open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusRankTwoDegreeCaps6401
open BCHKSTwoFrobeniusRankTwoClosure6401

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

/-- The `(A₀,A₁)` minor has the same sharp outer-degree cap as the existing
`(A₀,A₂)` numerator. -/
theorem coefficientRowMap_minor01_outer_natDegree_le
    {F : Type*} [Field F] (c d : SymbolicCoefficients F) :
    (symbolicMinor01 (coefficientRowMap c)
      (coefficientRowMap d)).natDegree ≤ 218453 := by
  have hc0 : ((coefficientRowMap c) 0).natDegree ≤ 174762 := by
    simpa [coefficientRowMap, a0XSlots6401] using
      (boxPolynomialMap_natDegree_le a0XSlots6401 symbolicDepth6401 c.1)
  have hd0 : ((coefficientRowMap d) 0).natDegree ≤ 174762 := by
    simpa [coefficientRowMap, a0XSlots6401] using
      (boxPolynomialMap_natDegree_le a0XSlots6401 symbolicDepth6401 d.1)
  have hc1 : ((coefficientRowMap c) 1).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a1XSlots6401] using
      (boxPolynomialMap_natDegree_le a1XSlots6401
        symbolicDepthOne6401 c.2.1)
  have hd1 : ((coefficientRowMap d) 1).natDegree ≤ 43691 := by
    simpa [coefficientRowMap, a1XSlots6401] using
      (boxPolynomialMap_natDegree_le a1XSlots6401
        symbolicDepthOne6401 d.2.1)
  unfold symbolicMinor01
  exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hc0 hd1))
    (Polynomial.natDegree_mul_le.trans (Nat.add_le_add hd0 hc1))

/-- Evaluation of the `(A₁,A₂)` minor commutes with outer evaluation. -/
theorem evalOuterAt_symbolicRankTwoDenominator
    {F : Type*} [Field F] (x : F) (c d : SymbolicRow F) :
    evalOuterAt x (symbolicRankTwoDenominator c d) =
      evalOuterAt x (c 1) * evalOuterAt x (d 2) -
        evalOuterAt x (d 1) * evalOuterAt x (c 2) := by
  simp [symbolicRankTwoDenominator, evalOuterAt]

/-- At one coordinate, the two exact kernel relations and the projected
minor identity force the `(A₀,A₁)` minor to vanish. -/
theorem evalOuterAt_minor01_eq_zero_of_kernel_and_denominator
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u₀ u₁ : Fin n6401 → F)
    (c d : SymbolicKernel sigma alpha u₀ u₁)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c.1) (coefficientRowMap d.1) = 0)
    (i : Fin n6401) :
    evalOuterAt (alpha i)
      (symbolicMinor01 (coefficientRowMap c.1)
        (coefficientRowMap d.1)) = 0 := by
  have hc := kernel_coordinate_relation_eq_zero sigma alpha u₀ u₁ c i
  have hd := kernel_coordinate_relation_eq_zero sigma alpha u₀ u₁ d i
  have hdenEval := congrArg (evalOuterAt (alpha i)) hden
  rw [evalOuterAt_symbolicRankTwoDenominator] at hdenEval
  simp only [evalOuterAt, Polynomial.eval_zero] at hdenEval
  unfold symbolicCoordinateRelation at hc hd
  simp only [symbolicMinor01, evalOuterAt, Polynomial.eval_sub,
    Polynomial.eval_mul] at *
  linear_combination
    (Polynomial.eval (Polynomial.C (alpha i))
      ((coefficientRowMap d.1) 1)) * hc -
    (Polynomial.eval (Polynomial.C (alpha i))
      ((coefficientRowMap c.1) 1)) * hd +
    (receivedFrobeniusZ sigma (u₀ i) (u₁ i)) * hdenEval

/-- The same coordinate argument forces the `(A₀,A₂)` minor to vanish. -/
theorem evalOuterAt_numerator_eq_zero_of_kernel_and_denominator
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u₀ u₁ : Fin n6401 → F)
    (c d : SymbolicKernel sigma alpha u₀ u₁)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c.1) (coefficientRowMap d.1) = 0)
    (i : Fin n6401) :
    evalOuterAt (alpha i)
      (symbolicRankTwoNumerator (coefficientRowMap c.1)
        (coefficientRowMap d.1)) = 0 := by
  have hc := kernel_coordinate_relation_eq_zero sigma alpha u₀ u₁ c i
  have hd := kernel_coordinate_relation_eq_zero sigma alpha u₀ u₁ d i
  have hdenEval := congrArg (evalOuterAt (alpha i)) hden
  rw [evalOuterAt_symbolicRankTwoDenominator] at hdenEval
  simp only [evalOuterAt, Polynomial.eval_zero] at hdenEval
  unfold symbolicCoordinateRelation at hc hd
  simp only [symbolicRankTwoNumerator, evalOuterAt, Polynomial.eval_sub,
    Polynomial.eval_mul] at *
  linear_combination
    (Polynomial.eval (Polynomial.C (alpha i))
      ((coefficientRowMap d.1) 2)) * hc -
    (Polynomial.eval (Polynomial.C (alpha i))
      ((coefficientRowMap c.1) 2)) * hd -
    (receivedZ (u₀ i) (u₁ i)) * hdenEval

/-- Vanishing on all distinct locators globalizes the `(A₀,A₁)` minor. -/
theorem symbolicMinor01_eq_zero_of_kernel_and_denominator
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (halpha : Function.Injective alpha)
    (u₀ u₁ : Fin n6401 → F)
    (c d : SymbolicKernel sigma alpha u₀ u₁)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c.1) (coefficientRowMap d.1) = 0) :
    symbolicMinor01 (coefficientRowMap c.1)
      (coefficientRowMap d.1) = 0 := by
  let roots : Finset (Polynomial F) :=
    Finset.univ.map
      ⟨fun i : Fin n6401 => Polynomial.C (alpha i),
        Polynomial.C_injective.comp halpha⟩
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (symbolicMinor01 (coefficientRowMap c.1)
      (coefficientRowMap d.1)) roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact evalOuterAt_minor01_eq_zero_of_kernel_and_denominator
      sigma alpha u₀ u₁ c d hden i
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact (coefficientRowMap_minor01_outer_natDegree_le c.1 d.1).trans_lt
      (by norm_num [n6401])

/-- Vanishing on all distinct locators globalizes the `(A₀,A₂)` minor. -/
theorem symbolicRankTwoNumerator_eq_zero_of_kernel_and_denominator
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (halpha : Function.Injective alpha)
    (u₀ u₁ : Fin n6401 → F)
    (c d : SymbolicKernel sigma alpha u₀ u₁)
    (hden : symbolicRankTwoDenominator
      (coefficientRowMap c.1) (coefficientRowMap d.1) = 0) :
    symbolicRankTwoNumerator (coefficientRowMap c.1)
      (coefficientRowMap d.1) = 0 := by
  let roots : Finset (Polynomial F) :=
    Finset.univ.map
      ⟨fun i : Fin n6401 => Polynomial.C (alpha i),
        Polynomial.C_injective.comp halpha⟩
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    (symbolicRankTwoNumerator (coefficientRowMap c.1)
      (coefficientRowMap d.1)) roots
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
    exact evalOuterAt_numerator_eq_zero_of_kernel_and_denominator
      sigma alpha u₀ u₁ c d hden i
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
    exact (coefficientRowMap_numerator_outer_natDegree_le c.1 d.1).trans_lt
      (by norm_num [n6401])

/-- The apparent projected-rank-one residual is full symbolic rank one:
all three exterior coordinates vanish for every pair of kernel rows. -/
theorem A1A2RankOneResidual_implies_fullSymbolicRankOne6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (halpha : Function.Injective alpha)
    (u₀ u₁ : Fin n6401 → F)
    (hres : SymbolicA1A2RankOneResidual6401 sigma alpha u₀ u₁) :
    ∀ c d : SymbolicKernel sigma alpha u₀ u₁,
      ¬ SymbolicRowPairIndependent
        (coefficientRowMap c.1) (coefficientRowMap d.1) := by
  intro c d hind
  have hden := hres c d
  have h01 := symbolicMinor01_eq_zero_of_kernel_and_denominator
    sigma alpha halpha u₀ u₁ c d hden
  have h02 := symbolicRankTwoNumerator_eq_zero_of_kernel_and_denominator
    sigma alpha halpha u₀ u₁ c d hden
  rcases hind with h | h | h
  · exact h h01
  · exact h h02
  · exact h hden

end BCHKSTwoFrobeniusFullRankOne6401
end ProximityPrize.SubmissionLower
