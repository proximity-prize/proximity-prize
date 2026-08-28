import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition

/-!
# Split interpolation-factor caps

The staircase interpolant naturally comes with two different seed bounds:
the coefficient hull controls the joint `Y + Z` degree, while a separate
argument gives a sharper `Z` degree.  This file keeps those two inputs
separate.  It does not change the existing coefficient box or any geometric
counting theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactSplitFactorCaps

open ContactFactorCaps ContactFactorCover ContactImplicitContactLift ContactInterpolation
open ContactSelectedSeedDecomposition
open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

/-- A coefficient-box hull supplies the `Y` and `R` budgets, while an
independent degree bound on the ambient polynomial supplies the sharper
summed `Z` budget. -/
theorem separated_factor_caps_of_prod_dvd_split_z {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin 4) K)
    (Q : MvPolynomial (Fin 4) K) (D w L s z : ℕ)
    (hw : 0 < w) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hQZ : Q.degreeOf (3 : Fin 4) ≤ z)
    (hdiv : (∏ j ∈ I, f j) ∣ Q) :
    (∑ j ∈ I, (f j).degreeOf (1 : Fin 4)) ≤ (D - 1) / w ∧
      (∑ j ∈ I, (f j).degreeOf (2 : Fin 4)) ≤ s ∧
      (∑ j ∈ I, (f j).degreeOf (3 : Fin 4)) ≤ z := by
  have hsum := separated_degree_budgets_of_prod_dvd I f Q hQ hdiv
  have hY := degreeOf_Y_le_of_mem_box Q D w L s hw hbox
  have hR := degreeOf_R_le_of_mem_box Q D w L s hbox
  exact ⟨hsum.1.trans hY, hsum.2.1.trans hR, hsum.2.2.trans hQZ⟩

/-- Each direct factor inherits the original coefficient hull and the
separate sharper `Z` cap. -/
theorem directFactor_data_split_z
    (Q F : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s z : ℕ) (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hQZ : Q.degreeOf (3 : Fin 4) ≤ z)
    (hF : F ∈ positiveRFactors Q) :
    Irreducible F ∧ 0 < F.degreeOf (2 : Fin 4) ∧
      F ∈ globalCoefficientBox K D w L s ∧
      F.degreeOf (3 : Fin 4) ≤ z := by
  obtain ⟨hirred, hdiv, hRpos⟩ := positiveRFactors_spec Q F hF
  refine ⟨hirred, hRpos,
    mem_globalCoefficientBox_of_dvd F Q D w L s hQ hdiv hbox, ?_⟩
  exact (degreeOf_le_of_dvd (3 : Fin 4) F Q hdiv hQ).trans hQZ

/-- The actual positive-`R` factor family consumes the hull's `Y` and `R`
budgets but only the separately supplied sharp `Z` budget. -/
theorem directFactor_input_budgets_split_z
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (D w L s z : ℕ) (hw : 0 < w)
    (hbox : Q ∈ globalCoefficientBox K D w L s)
    (hQZ : Q.degreeOf (3 : Fin 4) ≤ z) :
    (∑ F ∈ positiveRFactors Q, F.degreeOf (1 : Fin 4)) ≤ (D - 1) / w ∧
      (∑ F ∈ positiveRFactors Q, F.degreeOf (2 : Fin 4)) ≤ s ∧
      (∑ F ∈ positiveRFactors Q, F.degreeOf (3 : Fin 4)) ≤ z := by
  exact separated_factor_caps_of_prod_dvd_split_z
    (positiveRFactors Q) id Q D w L s z hw hQ hbox hQZ
    (positiveRFactors_product_dvd Q hQ)

end

end ProximityPrize.SubmissionLower.ContactSplitFactorCaps

#print axioms ProximityPrize.SubmissionLower.ContactSplitFactorCaps.separated_factor_caps_of_prod_dvd_split_z
#print axioms ProximityPrize.SubmissionLower.ContactSplitFactorCaps.directFactor_data_split_z
#print axioms ProximityPrize.SubmissionLower.ContactSplitFactorCaps.directFactor_input_budgets_split_z
