import ProximityPrize.SubmissionLower.LocatorDerivativeWeightDescent6803

/-!
# Coordinate caps for derivatives from cumulative locator weights

The grouped derivative-chain count chooses a derivative order separately on
each base curve component.  Its arithmetic must therefore use caps which are
uniform over every order at least one (for the regular predecessor) or two
(for the exceptional escape fibre).  These lemmas turn cumulative-weight
descent into the three ordinary coordinate bounds consumed by the incidence
APIs.
-/

namespace ProximityPrize.SubmissionLower.LocatorDerivativeDegreeCaps6803

open RCN081 RCN095 RCN130 RCN136 RCN156 RCN234 RCN313 RCN319
open LocatorDerivativeChain LocatorDerivativeWeightDescent6803
  LocatorFactorAggregate

noncomputable section

set_option autoImplicit false

variable {K Omega : Type} [Field K] [Field Omega]

theorem degreeY_le_middleCumulative (Q : MvPolynomial (Fin 4) K) :
    Q.degreeOf (1 : Fin 4) ≤ middle (originalCumulativeFlag Q) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  rw [show middle (originalCumulativeFlag Q) = wt residualYSWeights Q by
    simpa [middle] using (originalCumulativeFlag_cumulative Q).2.1]
  omega

theorem degreeR_le_allCumulative (Q : MvPolynomial (Fin 4) K) :
    Q.degreeOf (2 : Fin 4) ≤ (originalCumulativeFlag Q).all := by
  rw [RCN130.originalCumulativeFlag_all]

theorem degreeZ_le_totalCumulative (Q : MvPolynomial (Fin 4) K) :
    Q.degreeOf (3 : Fin 4) ≤ total (originalCumulativeFlag Q) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  rw [show total (originalCumulativeFlag Q) = wt residualTotalWeights Q by
    simpa [total] using (originalCumulativeFlag_cumulative Q).2.2]
  omega

theorem dR_degreeY_le_sub (F : MvPolynomial (Fin 4) K) (j : ℕ) :
    (dR j F).degreeOf (1 : Fin 4) ≤
      middle (originalCumulativeFlag F) - j := by
  exact (degreeY_le_middleCumulative (dR j F)).trans
    (dR_cumulative_weights_le_sub F j).2.1

theorem dR_degreeR_le_sub (F : MvPolynomial (Fin 4) K) (j : ℕ) :
    (dR j F).degreeOf (2 : Fin 4) ≤
      (originalCumulativeFlag F).all - j := by
  exact (degreeR_le_allCumulative (dR j F)).trans
    (dR_cumulative_weights_le_sub F j).1

theorem dR_degreeZ_le_sub (F : MvPolynomial (Fin 4) K) (j : ℕ) :
    (dR j F).degreeOf (3 : Fin 4) ≤
      total (originalCumulativeFlag F) - j := by
  exact (degreeZ_le_totalCumulative (dR j F)).trans
    (dR_cumulative_weights_le_sub F j).2.2

/-- Uniform three-coordinate cap for the surface of `dR j F`. -/
theorem surfaceMap_dR_degreeOf_le_sub
    (phi : Polynomial K →+* Omega)
    (F : MvPolynomial (Fin 4) K) (j : ℕ) (i : Fin 3) :
    (surfaceMap phi (dR j F)).degreeOf i ≤
      ![middle (originalCumulativeFlag F) - j,
        (originalCumulativeFlag F).all - j,
        total (originalCumulativeFlag F) - j] i := by
  fin_cases i
  · exact (surfaceMap_degreeOf_le phi (dR j F) 0).trans
      (dR_degreeY_le_sub F j)
  · exact (surfaceMap_degreeOf_le phi (dR j F) 1).trans
      (dR_degreeR_le_sub F j)
  · exact (surfaceMap_degreeOf_le phi (dR j F) 2).trans
      (dR_degreeZ_le_sub F j)

end

end ProximityPrize.SubmissionLower.LocatorDerivativeDegreeCaps6803
