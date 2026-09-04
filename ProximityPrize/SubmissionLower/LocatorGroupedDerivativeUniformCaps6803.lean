import ProximityPrize.SubmissionLower.LocatorPositiveFactorGroupedAggregate6803

/-!
# Uniform caps for grouped derivative incidence

This file turns one cumulative `(middle, slope, total)` box on a locator into
the common coordinate boxes used by every active first-escape component.  It
also aggregates the mixed-degree budget over all original positive-`R`
irreducible factors, without a factor-count multiplier.
-/

namespace ProximityPrize.SubmissionLower.LocatorGroupedDerivativeUniformCaps6803

open scoped Classical BigOperators
open RCN001 RCN052 RCN068 RCN081 RCN082 RCN095 RCN130 RCN135 RCN136 RCN137
  RCN138 RCN156 RCN167 RCN222 RCN234 RCN238 RCN260 RCN267 RCN313 RCN319
open LocatorDerivativeChain LocatorDerivativeDegreeCaps6803 LocatorFactorAggregate
  LocatorGroupedDerivativeIncidence6803 LocatorPositiveFactorGroupedAggregate6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000

variable {K : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K

/-- Mixed-degree budget for an initial factor in the cumulative box
`(middle,slope,total) = (Y,S,L)` and its first `R` derivative. -/
def positiveDerivativeMixedBudget (yCap sCap lCap : ℕ) : Fin 3 → ℕ :=
  ![sCap * (lCap - 1) + lCap * (sCap - 1),
    yCap * (lCap - 1) + lCap * (yCap - 1),
    yCap * (sCap - 1) + sCap * (yCap - 1)]

def originalSurfaceCap (yCap sCap lCap : ℕ) : Fin 3 → ℕ :=
  ![yCap, sCap, lCap]

def firstDerivativeSurfaceCap (yCap sCap lCap : ℕ) : Fin 3 → ℕ :=
  ![yCap - 1, sCap - 1, lCap - 1]

def activeCarrierAgreementCap (w yCap sCap lCap : ℕ) : Fin 3 → ℕ :=
  ![1 + 2 * w * (yCap - 1),
    w * (2 * (sCap - 1) - 1),
    2 * w * (lCap - 1) + 1]

def activeEscapeSurfaceCap (yCap sCap lCap : ℕ) : Fin 3 → ℕ :=
  ![yCap - 2, sCap - 2, lCap - 2]

/-- A dummy unequal-parameter record used only to invoke the existing
geometric-factor mixed-degree summation theorem. -/
private def derivativePairParameters (yCap sCap lCap : ℕ) : UnequalParameters :=
  ⟨0, 0, 0, 0, 0, 0, yCap - 1, sCap - 1, lCap - 1⟩

theorem positiveFactor_middle_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (yCap : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q) :
    middle (originalCumulativeFlag F) ≤ yCap := by
  rw [show middle (originalCumulativeFlag F) = wt residualYSWeights F by
    simpa [middle] using (originalCumulativeFlag_cumulative F).2.1]
  exact (weightedTotalDegree_le_of_dvd residualYSWeights F Q
    (positiveRFactors_spec Q F hF).2.1 hQ).trans hY

theorem positiveFactor_slope_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (sCap : ℕ)
    (hS : wt residualSWeights Q ≤ sCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q) :
    (originalCumulativeFlag F).all ≤ sCap := by
  rw [(originalCumulativeFlag_cumulative F).1]
  exact (weightedTotalDegree_le_of_dvd residualSWeights F Q
    (positiveRFactors_spec Q F hF).2.1 hQ).trans hS

theorem positiveFactor_total_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (lCap : ℕ)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q) :
    total (originalCumulativeFlag F) ≤ lCap := by
  rw [show total (originalCumulativeFlag F) = wt residualTotalWeights F by
    simpa [total] using (originalCumulativeFlag_cumulative F).2.2]
  exact (weightedTotalDegree_le_of_dvd residualTotalWeights F Q
    (positiveRFactors_spec Q F hF).2.1 hQ).trans hL

theorem positiveFactor_dR_one_degreeY_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (yCap : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q) :
    (dR 1 F).degreeOf (1 : Fin 4) ≤ yCap - 1 := by
  exact (dR_degreeY_le_sub F 1).trans
    (Nat.sub_le_sub_right (positiveFactor_middle_le Q hQ yCap hY F hF) 1)

theorem positiveFactor_dR_one_degreeR_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (sCap : ℕ)
    (hS : wt residualSWeights Q ≤ sCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q) :
    (dR 1 F).degreeOf (2 : Fin 4) ≤ sCap - 1 := by
  exact (dR_degreeR_le_sub F 1).trans
    (Nat.sub_le_sub_right (positiveFactor_slope_le Q hQ sCap hS F hF) 1)

theorem positiveFactor_dR_one_degreeZ_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (lCap : ℕ)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q) :
    (dR 1 F).degreeOf (3 : Fin 4) ≤ lCap - 1 := by
  exact (dR_degreeZ_le_sub F 1).trans
    (Nat.sub_le_sub_right (positiveFactor_total_le Q hQ lCap hL F hF) 1)

theorem active_componentEscapeIndex_two_le
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hactive : (componentGenericSeeds F selected Gamma g C ∪
      componentExceptionalSeeds F selected Gamma g C).Nonempty) :
    2 ≤ componentEscapeIndex F selected Gamma g C := by
  have hDelta := initialComponentSeeds_nonempty_of_partition_nonempty
    F selected Gamma g C hactive
  obtain ⟨E, hE⟩ := componentEscapeIndex_certificate
    F selected Gamma g C hDelta
  rw [← hE]
  exact E.two_le

theorem active_componentCarrier_degreeOf_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (yCap sCap lCap : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hactive : (componentGenericSeeds F selected Gamma g C ∪
      componentExceptionalSeeds F selected Gamma g C).Nonempty)
    (j : Fin 3) :
    (componentCarrier F selected Gamma g C).degreeOf j.succ ≤
      firstDerivativeSurfaceCap yCap sCap lCap j := by
  have hindex := active_componentEscapeIndex_two_le F selected Gamma g C hactive
  have hFY := positiveFactor_middle_le Q hQ yCap hY F hF
  have hFS := positiveFactor_slope_le Q hQ sCap hS F hF
  have hFL := positiveFactor_total_le Q hQ lCap hL F hF
  unfold componentCarrier
  fin_cases j
  · have h := dR_degreeY_le_sub F
      (componentEscapeIndex F selected Gamma g C - 1)
    change (dR (componentEscapeIndex F selected Gamma g C - 1) F).degreeOf
      (1 : Fin 4) ≤ yCap - 1
    omega
  · have h := dR_degreeR_le_sub F
      (componentEscapeIndex F selected Gamma g C - 1)
    change (dR (componentEscapeIndex F selected Gamma g C - 1) F).degreeOf
      (2 : Fin 4) ≤ sCap - 1
    omega
  · have h := dR_degreeZ_le_sub F
      (componentEscapeIndex F selected Gamma g C - 1)
    change (dR (componentEscapeIndex F selected Gamma g C - 1) F).degreeOf
      (3 : Fin 4) ≤ lCap - 1
    omega

theorem active_componentCarrier_pderiv_eq
    (F : MvPolynomial (Fin 4) K)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hactive : (componentGenericSeeds F selected Gamma g C ∪
      componentExceptionalSeeds F selected Gamma g C).Nonempty) :
    MvPolynomial.pderiv (2 : Fin 4)
      (componentCarrier F selected Gamma g C) =
        dR (componentEscapeIndex F selected Gamma g C) F := by
  have hindex := active_componentEscapeIndex_two_le F selected Gamma g C hactive
  calc
    _ = dR (componentEscapeIndex F selected Gamma g C - 1 + 1) F := by
      rw [componentCarrier, dR_succ]
    _ = _ := by congr 1 <;> omega

theorem active_componentEscape_degreeOf_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (yCap sCap lCap : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hactive : (componentGenericSeeds F selected Gamma g C ∪
      componentExceptionalSeeds F selected Gamma g C).Nonempty)
    (j : Fin 3) :
    (surfaceMap (polynomialEmbedding K)
      (MvPolynomial.pderiv (2 : Fin 4)
        (componentCarrier F selected Gamma g C))).degreeOf j ≤
      activeEscapeSurfaceCap yCap sCap lCap j := by
  rw [active_componentCarrier_pderiv_eq F selected Gamma g C hactive]
  have hindex := active_componentEscapeIndex_two_le F selected Gamma g C hactive
  have hFY := positiveFactor_middle_le Q hQ yCap hY F hF
  have hFS := positiveFactor_slope_le Q hQ sCap hS F hF
  have hFL := positiveFactor_total_le Q hQ lCap hL F hF
  fin_cases j
  · change (surfaceMap (polynomialEmbedding K)
      (dR (componentEscapeIndex F selected Gamma g C) F)).degreeOf 0 ≤
        yCap - 2
    have h := surfaceMap_dR_degreeOf_le_sub (polynomialEmbedding K) F
      (componentEscapeIndex F selected Gamma g C) 0
    change (surfaceMap (polynomialEmbedding K)
      (dR (componentEscapeIndex F selected Gamma g C) F)).degreeOf 0 ≤
        middle (originalCumulativeFlag F) -
          componentEscapeIndex F selected Gamma g C at h
    omega
  · change (surfaceMap (polynomialEmbedding K)
      (dR (componentEscapeIndex F selected Gamma g C) F)).degreeOf 1 ≤
        sCap - 2
    have h := surfaceMap_dR_degreeOf_le_sub (polynomialEmbedding K) F
      (componentEscapeIndex F selected Gamma g C) 1
    change (surfaceMap (polynomialEmbedding K)
      (dR (componentEscapeIndex F selected Gamma g C) F)).degreeOf 1 ≤
        (originalCumulativeFlag F).all -
          componentEscapeIndex F selected Gamma g C at h
    omega
  · change (surfaceMap (polynomialEmbedding K)
      (dR (componentEscapeIndex F selected Gamma g C) F)).degreeOf 2 ≤
        lCap - 2
    have h := surfaceMap_dR_degreeOf_le_sub (polynomialEmbedding K) F
      (componentEscapeIndex F selected Gamma g C) 2
    change (surfaceMap (polynomialEmbedding K)
      (dR (componentEscapeIndex F selected Gamma g C) F)).degreeOf 2 ≤
        total (originalCumulativeFlag F) -
          componentEscapeIndex F selected Gamma g C at h
    omega

theorem active_componentAgreement_degreeOf_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (yCap sCap lCap w : ℕ) (hsCap : 2 ≤ sCap)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (g : GeometricFactor K F) (C : InitialComponent F g)
    (hactive : (componentGenericSeeds F selected Gamma g C ∪
      componentExceptionalSeeds F selected Gamma g C).Nonempty)
    (x u0 u1 : K) (j : Fin 3) :
    (agreementPolynomial (polynomialEmbedding K)
      (componentCarrier F selected Gamma g C) w x u0 u1).degreeOf j ≤
        activeCarrierAgreementCap w yCap sCap lCap j := by
  have hcarrier := active_componentCarrier_degreeOf_le Q hQ yCap sCap lCap
    hY hS hL F hF selected Gamma g C hactive
  have hcaps := surface_agreement_caps (polynomialEmbedding K)
    (componentCarrier F selected Gamma g C)
    (yCap - 1) (sCap - 1) (lCap - 1) (by omega)
    (hcarrier 0) (hcarrier 1) (hcarrier 2) w
    (fun n ↦ (n.factorial : K)⁻¹) x u0 u1 j
  simpa only [agreementPolynomial, HasCaps, capAt, agreementCaps,
    activeCarrierAgreementCap, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] using hcaps

theorem positiveGeometricFactor_degreeOf_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (yCap sCap lCap : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (g : GeometricFactor K F) (j : Fin 3) :
    g.1.degreeOf j ≤ originalSurfaceCap yCap sCap lCap j := by
  have hgeom := geometricFactor_degree_le K F
    (positiveRFactors_spec Q F hF).1.ne_zero g j
  have hFY := (degreeY_le_middleCumulative F).trans
    (positiveFactor_middle_le Q hQ yCap hY F hF)
  have hFS := (degreeR_le_allCumulative F).trans
    (positiveFactor_slope_le Q hQ sCap hS F hF)
  have hFL := (degreeZ_le_totalCumulative F).trans
    (positiveFactor_total_le Q hQ lCap hL F hF)
  fin_cases j
  · exact hgeom.trans hFY
  · exact hgeom.trans hFS
  · exact hgeom.trans hFL

theorem positiveFactor_dR_one_surface_degreeOf_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (yCap sCap lCap : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (j : Fin 3) :
    (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf j ≤
      firstDerivativeSurfaceCap yCap sCap lCap j := by
  fin_cases j
  · exact (surfaceMap_degreeOf_le (polynomialEmbedding K) (dR 1 F) 0).trans
      (positiveFactor_dR_one_degreeY_le Q hQ yCap hY F hF)
  · exact (surfaceMap_degreeOf_le (polynomialEmbedding K) (dR 1 F) 1).trans
      (positiveFactor_dR_one_degreeR_le Q hQ sCap hS F hF)
  · exact (surfaceMap_degreeOf_le (polynomialEmbedding K) (dR 1 F) 2).trans
      (positiveFactor_dR_one_degreeZ_le Q hQ lCap hL F hF)

theorem positiveGeometricFactor_derivative_proper
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (sCap p : ℕ) [CharP K p]
    (hS : wt residualSWeights Q ≤ sCap) (hsmall : sCap < p)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (g : GeometricFactor K F) :
    ¬ g.1 ∣ surfaceMap (polynomialEmbedding K) (dR 1 F) := by
  have hspec := positiveRFactors_spec Q F hF
  have hFsmall : F.degreeOf (2 : Fin 4) < p :=
    (degreeR_le_allCumulative F |>.trans
      (positiveFactor_slope_le Q hQ sCap hS F hF)).trans_lt hsmall
  obtain ⟨hgirred, hgdiv⟩ :=
    surfaceFactors_spec (polynomialEmbedding K) F g.1 g.2
  have hproper := H_proper_on_every_geometric_factor K (GenericField K)
    F hspec.1 p hspec.2.2 hFsmall g.1 hgirred
    (by simpa only [canonical_geometricSurfaceMap] using hgdiv)
  have hdR : dR 1 F = MvPolynomial.pderiv (2 : Fin 4) F := by
    simpa only [Nat.zero_add, dR_zero] using dR_succ 0 F
  rw [hdR]
  simpa only [canonical_geometricSurfaceMap] using hproper

theorem positiveGeometricFactor_degree_lt_char
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (yCap sCap lCap p : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (hySmall : yCap < p) (hsSmall : sCap < p) (hlSmall : lCap < p)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (g : GeometricFactor K F) (j : Fin 3) :
    g.1.degreeOf j < p := by
  have hdegree := positiveGeometricFactor_degreeOf_le Q hQ yCap sCap lCap
    hY hS hL F hF g j
  fin_cases j
  · exact hdegree.trans_lt hySmall
  · exact hdegree.trans_lt hsSmall
  · exact hdegree.trans_lt hlSmall

/-- A cap-level characteristic gate implies every actual two-coordinate
mixed-degree gate needed by the initial component family. -/
theorem positiveGeometricFactor_cutDegree_lt_char
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (yCap sCap lCap p : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (hmixed : ∀ j k : Fin 3, j ≠ k →
      firstDerivativeSurfaceCap yCap sCap lCap j *
          originalSurfaceCap yCap sCap lCap k +
        originalSurfaceCap yCap sCap lCap j *
          firstDerivativeSurfaceCap yCap sCap lCap k < p)
    (F : MvPolynomial (Fin 4) K) (hF : F ∈ positiveRFactors Q)
    (g : GeometricFactor K F) (j k : Fin 3) (hjk : j ≠ k) :
    (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf j *
          g.1.degreeOf k +
        g.1.degreeOf j *
          (surfaceMap (polynomialEmbedding K) (dR 1 F)).degreeOf k < p := by
  apply lt_of_le_of_lt _ (hmixed j k hjk)
  exact Nat.add_le_add
    (Nat.mul_le_mul
      (positiveFactor_dR_one_surface_degreeOf_le Q hQ yCap sCap lCap
        hY hS hL F hF j)
      (positiveGeometricFactor_degreeOf_le Q hQ yCap sCap lCap
        hY hS hL F hF g k))
    (Nat.mul_le_mul
      (positiveGeometricFactor_degreeOf_le Q hQ yCap sCap lCap
        hY hS hL F hF g j)
      (positiveFactor_dR_one_surface_degreeOf_le Q hQ yCap sCap lCap
        hY hS hL F hF k))

/-- The mixed-degree budget for all initial pairs `(g,dR F)`, summed over
all geometric factors `g` and all positive-`R` factors `F`, is controlled by
one cumulative box on `Q`. -/
theorem allPositiveFactors_mixedDegree_le
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0) (yCap sCap lCap : ℕ)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (j : Fin 3) :
    (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
      coordinateMixedDegree (GenericField K) g.1
        (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) ≤
      positiveDerivativeMixedBudget yCap sCap lCap j := by
  classical
  let P := derivativePairParameters yCap sCap lCap
  have hsingle (F : MvPolynomial (Fin 4) K)
      (hF : F ∈ positiveRFactors Q) :
      (∑ g : GeometricFactor K F,
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) ≤
        regularCapAt (regularVector P F) j := by
    exact sum_coordinateMixedDegree_geometricFactors_le P F (dR 1 F)
      (positiveRFactors_spec Q F hF).1.ne_zero
      (positiveFactor_dR_one_degreeY_le Q hQ yCap hY F hF)
      (positiveFactor_dR_one_degreeR_le Q hQ sCap hS F hF)
      (positiveFactor_dR_one_degreeZ_le Q hQ lCap hL F hF) j
  have hsumY := sum_degreeOf_le_of_prod_dvd (positiveRFactors Q) id Q hQ
    (positiveRFactors_product_dvd Q hQ) (1 : Fin 4)
  have hsumR := sum_degreeOf_le_of_prod_dvd (positiveRFactors Q) id Q hQ
    (positiveRFactors_product_dvd Q hQ) (2 : Fin 4)
  have hsumZ := sum_degreeOf_le_of_prod_dvd (positiveRFactors Q) id Q hQ
    (positiveRFactors_product_dvd Q hQ) (3 : Fin 4)
  have hsumY' : (∑ F ∈ positiveRFactors Q,
      F.degreeOf (1 : Fin 4)) ≤ Q.degreeOf (1 : Fin 4) := by
    simpa only [id_eq] using hsumY
  have hsumR' : (∑ F ∈ positiveRFactors Q,
      F.degreeOf (2 : Fin 4)) ≤ Q.degreeOf (2 : Fin 4) := by
    simpa only [id_eq] using hsumR
  have hsumZ' : (∑ F ∈ positiveRFactors Q,
      F.degreeOf (3 : Fin 4)) ≤ Q.degreeOf (3 : Fin 4) := by
    simpa only [id_eq] using hsumZ
  have hQY : Q.degreeOf (1 : Fin 4) ≤ yCap :=
    (degreeY_le_middleCumulative Q).trans (by
      rw [show middle (originalCumulativeFlag Q) = wt residualYSWeights Q by
        simpa [middle] using (originalCumulativeFlag_cumulative Q).2.1]
      exact hY)
  have hQR : Q.degreeOf (2 : Fin 4) ≤ sCap := by
    rw [← originalCumulativeFlag_all]
    rw [(originalCumulativeFlag_cumulative Q).1]
    exact hS
  have hQZ : Q.degreeOf (3 : Fin 4) ≤ lCap :=
    (degreeZ_le_totalCumulative Q).trans (by
      rw [show total (originalCumulativeFlag Q) = wt residualTotalWeights Q by
        simpa [total] using (originalCumulativeFlag_cumulative Q).2.2]
      exact hL)
  calc
    (∑ F ∈ positiveRFactors Q, ∑ g : GeometricFactor K F,
        coordinateMixedDegree (GenericField K) g.1
          (surfaceMap (polynomialEmbedding K) (dR 1 F)) j) ≤
      ∑ F ∈ positiveRFactors Q, regularCapAt (regularVector P F) j :=
        Finset.sum_le_sum fun F hF ↦ hsingle F hF
    _ ≤ positiveDerivativeMixedBudget yCap sCap lCap j := by
      fin_cases j
      · change (∑ F ∈ positiveRFactors Q,
          (F.degreeOf (2 : Fin 4) * (lCap - 1) +
            F.degreeOf (3 : Fin 4) * (sCap - 1))) ≤
          sCap * (lCap - 1) + lCap * (sCap - 1)
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        exact Nat.add_le_add
          (Nat.mul_le_mul_right (lCap - 1) (hsumR'.trans hQR))
          (Nat.mul_le_mul_right (sCap - 1) (hsumZ'.trans hQZ))
      · change (∑ F ∈ positiveRFactors Q,
          (F.degreeOf (1 : Fin 4) * (lCap - 1) +
            F.degreeOf (3 : Fin 4) * (yCap - 1))) ≤
          yCap * (lCap - 1) + lCap * (yCap - 1)
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        exact Nat.add_le_add
          (Nat.mul_le_mul_right (lCap - 1) (hsumY'.trans hQY))
          (Nat.mul_le_mul_right (yCap - 1) (hsumZ'.trans hQZ))
      · change (∑ F ∈ positiveRFactors Q,
          (F.degreeOf (1 : Fin 4) * (sCap - 1) +
            F.degreeOf (2 : Fin 4) * (yCap - 1))) ≤
          yCap * (sCap - 1) + sCap * (yCap - 1)
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
        exact Nat.add_le_add
          (Nat.mul_le_mul_right (sCap - 1) (hsumY'.trans hQY))
          (Nat.mul_le_mul_right (yCap - 1) (hsumR'.trans hQR))

/-- Concrete cumulative-box instantiation of the all-positive-factor grouped
bound.  Only the global seed hypotheses and elementary cap-level
characteristic inequalities remain for the caller. -/
theorem allPositiveExactChainSeeds_grouped_of_cumulativeCaps
    {Iota : Type}
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes)
    (p w a errors yCap sCap lCap : ℕ) [CharP K p]
    (hw : 1 ≤ w) (hchar : w < p) (hwa : w < a)
    (han : a ≤ nodes.card) (hsCap : 2 ≤ sCap)
    (hY : wt residualYSWeights Q ≤ yCap)
    (hS : wt residualSWeights Q ≤ sCap)
    (hL : wt residualTotalWeights Q ≤ lCap)
    (hySmall : yCap < p) (hsSmall : sCap < p) (hlSmall : lCap < p)
    (hmixed : ∀ j k : Fin 3, j ≠ k →
      firstDerivativeSurfaceCap yCap sCap lCap j *
          originalSurfaceCap yCap sCap lCap k +
        originalSurfaceCap yCap sCap lCap j *
          firstDerivativeSurfaceCap yCap sCap lCap k < p)
    (hdegree : ∀ gamma ∈ allPositiveExactChainSeeds Q selected Gamma,
      (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ allPositiveExactChainSeeds Q selected Gamma,
      a ≤ (nodes.filter fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i).card)
    (hnoPencil : NoLargeSelectedPencil selected
      (allPositiveExactChainSeeds Q selected Gamma) w errors) :
    (allPositiveExactChainSeeds Q selected Gamma).card * (a - w) ≤
      (nodes.card - w) *
          (∑ j, activeCarrierAgreementCap w yCap sCap lCap j *
            positiveDerivativeMixedBudget yCap sCap lCap j) +
        (errors + 1) * (a - w) *
          positiveDerivativeMixedBudget yCap sCap lCap 2 +
        (a - w) *
          (∑ j, activeEscapeSurfaceCap yCap sCap lCap j *
            positiveDerivativeMixedBudget yCap sCap lCap j) := by
  apply allPositiveExactChainSeeds_grouped_card_le Q selected Gamma
    nodes x u0 u1 hinj p w a errors hw hchar hwa han
    hdegree hagreement hnoPencil
  · intro F hF g
    exact positiveGeometricFactor_derivative_proper Q hQ sCap p hS hsSmall
      F hF g
  · intro F hF g j
    exact positiveGeometricFactor_degree_lt_char Q hQ yCap sCap lCap p
      hY hS hL hySmall hsSmall hlSmall F hF g j
  · intro F hF g j k hjk
    exact positiveGeometricFactor_cutDegree_lt_char Q hQ yCap sCap lCap p
      hY hS hL hmixed F hF g j k hjk
  · intro F hF g C hactive i hi j
    exact active_componentAgreement_degreeOf_le Q hQ yCap sCap lCap w hsCap
      hY hS hL F hF selected Gamma g C hactive (x i) (u0 i) (u1 i) j
  · intro F hF g C hactive j
    exact active_componentEscape_degreeOf_le Q hQ yCap sCap lCap
      hY hS hL F hF selected Gamma g C hactive j
  · exact allPositiveFactors_mixedDegree_le Q hQ yCap sCap lCap hY hS hL

namespace Concrete

def fixedMixedBudget : Fin 3 → ℕ :=
  positiveDerivativeMixedBudget 153 34 6676

def residualBMixedBudget : Fin 3 → ℕ :=
  positiveDerivativeMixedBudget 153 34 14261

def residualTMixedBudget : Fin 3 → ℕ :=
  positiveDerivativeMixedBudget 250 56 6679

theorem fixedMixedBudget_eq :
    fixedMixedBudget = ![447258, 2036027, 10217] := by
  native_decide

theorem residualBMixedBudget_eq :
    residualBMixedBudget = ![955453, 4349452, 10217] := by
  native_decide

theorem residualTMixedBudget_eq :
    residualTMixedBudget = ![741313, 3332571, 27694] := by
  native_decide

theorem fixed_pair_characteristic_gate :
    ∀ j k : Fin 3, j ≠ k →
      firstDerivativeSurfaceCap 153 34 6676 j *
          originalSurfaceCap 153 34 6676 k +
        originalSurfaceCap 153 34 6676 j *
          firstDerivativeSurfaceCap 153 34 6676 k < 2130706433 := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;>
    simp_all [firstDerivativeSurfaceCap, originalSurfaceCap] <;> norm_num

theorem residualB_pair_characteristic_gate :
    ∀ j k : Fin 3, j ≠ k →
      firstDerivativeSurfaceCap 153 34 14261 j *
          originalSurfaceCap 153 34 14261 k +
        originalSurfaceCap 153 34 14261 j *
          firstDerivativeSurfaceCap 153 34 14261 k < 2130706433 := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;>
    simp_all [firstDerivativeSurfaceCap, originalSurfaceCap] <;> norm_num

theorem residualT_pair_characteristic_gate :
    ∀ j k : Fin 3, j ≠ k →
      firstDerivativeSurfaceCap 250 56 6679 j *
          originalSurfaceCap 250 56 6679 k +
        originalSurfaceCap 250 56 6679 j *
          firstDerivativeSurfaceCap 250 56 6679 k < 2130706433 := by
  intro j k hjk
  fin_cases j <;> fin_cases k <;>
    simp_all [firstDerivativeSurfaceCap, originalSurfaceCap] <;> norm_num

theorem fixed_agreement_cap_eq :
    activeCarrierAgreementCap 131071 153 34 6676 =
      ![39845585, 8519615, 1749797851] := by
  native_decide

theorem residualB_agreement_cap_eq :
    activeCarrierAgreementCap 131071 153 34 14261 =
      ![39845585, 8519615, 3738144921] := by
  native_decide

theorem residualT_agreement_cap_eq :
    activeCarrierAgreementCap 131071 250 56 6679 =
      ![65273359, 14286739, 1750584277] := by
  native_decide

theorem fixed_escape_cap_eq :
    activeEscapeSurfaceCap 153 34 6676 = ![151, 32, 6674] := by
  native_decide

theorem residualB_escape_cap_eq :
    activeEscapeSurfaceCap 153 34 14261 = ![151, 32, 14259] := by
  native_decide

theorem residualT_escape_cap_eq :
    activeEscapeSurfaceCap 250 56 6679 = ![248, 54, 6677] := by
  native_decide

end Concrete

end

end ProximityPrize.SubmissionLower.LocatorGroupedDerivativeUniformCaps6803
