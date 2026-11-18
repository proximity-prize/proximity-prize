/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/- Modified for the second Hasse-jet coordinate; original contributors under Apache 2.0. -/
import ProximityPrize.SubmissionLower.Mid6833WeightTaylor
import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
import ArkLib.Data.Polynomial.Differential.RationalTaylorDerivativeDegree
open MvPolynomial
namespace PolynomialDifferential
noncomputable section
variable {F : Type*}
theorem degreeOf_commonTaylorNumerator_secondOrder_weighted [Field F] (center : F)
    (Q : DifferentialPolynomial F 2) (v K τ : ℕ)
    (hτ : TaylorExponentSufficient 2 K τ) (hv : 2 ≤ v)
    (hjet : Q.weightedTotalDegree (indexWeight 3) ≤ v) (l : Fin K) :
    (commonTaylorNumerator center Q τ l.val).degreeOf 2 ≤ (τ * (v - 2) + l.val)/2 := by
  let Qover : DifferentialPolynomial (Polynomial F) 2 := MvPolynomial.map Polynomial.C Q
  have hQover : Qover.weightedTotalDegree (indexWeight 3) ≤ v := by
    rw [weightedTotalDegree,Finset.sup_le_iff] at hjet ⊢
    intro e he
    exact hjet e (MvPolynomial.support_map_subset _ _ he)
  have hover := degreeOf_le_index_quotient _ (Fin.last 2) (by decide) (weighted_padded_numerator (Polynomial.C center) Qover v K τ hτ hv hQover l)
  have hmap :
      (MvPolynomial.map (Polynomial.aeval (0 : F)).toRingHom
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Qover τ l.val)).degreeOf 2 ≤
        (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Qover τ l.val).degreeOf 2 := by
    simp only [MvPolynomial.degreeOf_def]
    exact Multiset.count_le_of_le 2
      (MvPolynomial.degrees_map_le
        (p := commonTaylorNumeratorOver (F := F) (Polynomial.C center) Qover τ l.val)
        (f := (Polynomial.aeval (0 : F)).toRingHom))
  have hQeval :
      MvPolynomial.map (Polynomial.aeval (0 : F)).toRingHom Qover = Q := by
    dsimp only [Qover]
    rw [MvPolynomial.map_map]
    have he : (Polynomial.aeval (0 : F)).toRingHom.comp Polynomial.C = RingHom.id F := by
      ext x
      simp
    rw [he]
    exact MvPolynomial.map_id Q
  have hspec := map_commonTaylorNumeratorOver_eq
    (F := F) (φ := Polynomial.aeval (0 : F)) (Polynomial.C center) Qover τ l.val
  rw [hQeval] at hspec
  have hspec' :
      MvPolynomial.map (Polynomial.aeval (0 : F)).toRingHom
          (commonTaylorNumeratorOver (F := F) (Polynomial.C center) Qover τ l.val) =
        commonTaylorNumerator center Q τ l.val := by
    simpa using hspec
  rw [← hspec']
  exact hmap.trans hover


theorem degreeOf_agreement_secondOrder_weighted [Field F] (center : F)
    (Q : DifferentialPolynomial F 2) (v K τ : ℕ) (hτ : TaylorExponentSufficient 2 K τ)
    (hv : 2 ≤ v) (hQ : Q.weightedTotalDegree (indexWeight 3) ≤ v) (x y : F) :
    (taylorAgreementEquation center Q K x y (τ := τ)).degreeOf 2 ≤ (τ*(v-2)+(K-1))/2 := by
  have hdegree : Q.degreeOf (some (Fin.last 2)) ≤ v :=
    (degreeOf_le_weightedTotalDegree _ _ (by simp [indexWeight]) Q).trans hQ
  unfold taylorAgreementEquation
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro l _
    apply (degreeOf_mul_le _ _ _).trans
    simp only [degreeOf_C, zero_add]
    exact (degreeOf_commonTaylorNumerator_secondOrder_weighted center Q v K τ hτ hv hQ l).trans (by omega)
  · apply (degreeOf_mul_le _ _ _).trans
    simp only [degreeOf_C, zero_add]
    have hs := (weighted_initial_separant center Q).trans (Nat.sub_le_sub_right hQ 2)
    have hp := (weightedTotalDegree_pow_le Fin.val (initialJetSeparant center Q) τ).trans
      (Nat.mul_le_mul_left τ hs)
    apply degreeOf_le_index_quotient _ (Fin.last 2) (by decide)
    exact hp.trans (Nat.le_add_right _ _)

#print axioms degreeOf_commonTaylorNumerator_secondOrder_weighted
#print axioms degreeOf_agreement_secondOrder_weighted
end
end PolynomialDifferential
