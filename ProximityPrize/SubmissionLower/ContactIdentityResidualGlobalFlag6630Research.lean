import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch
import ProximityPrize.SubmissionLower.ContactSharpTotalAgreement

/-!
# Score-66.42 global residual flag

This module instantiates the cap-independent global residual transform at the
score-66.42 surface cumulative flag

`S <= 8`, `Y + S <= 40`, `Y + S + R <= 617`.

The corresponding agreement cut has cumulative bounds
`R <= 15*d`, `Y + R <= 1 + 78*d`, and
`Z + Y + R <= 1 + 1233*d`, hence nested flag
`(1155*d, 1 + 63*d, 15*d)`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research

open scoped Classical BigOperators
open ContactIdentityResidualGlobalTransformResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactPost6464ShearSupportResearch
open ContactFlagBezout6543Research
open ContactNearPencil6630FlagResearch
open ContactGenericSurface ContactTaylorNumerators
open ContactSharpTotalAgreement

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-- The score-66.42 surface cumulative flag is preserved by every global
nodal residual transform. -/
theorem globalResidualHom_surface_flag_weights6630
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617) :
    wt residualSWeights (globalResidualHom P0 P1 V F) ≤ 8 ∧
      wt residualYSWeights (globalResidualHom P0 P1 V F) ≤ 40 ∧
      wt residualTotalWeights (globalResidualHom P0 P1 V F) ≤ 617 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_s] using hS)
  · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_ys] using hYS)
  · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_total] using hTotal)

/-- Exact cumulative agreement-cut bounds for the score-66.42 surface. -/
theorem globalResidual_agreement_weight_bounds6630
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    (agreementNumerator (globalResidualHom P0 P1 V F)
        d coeffs x u0 u1).degreeOf (2 : Fin 4) ≤ 15 * d ∧
      wt residualYSWeights
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1) ≤ 1 + 78 * d ∧
      wt residualTotalWeights
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1) ≤ 1 + 1233 * d := by
  let Fres := globalResidualHom P0 P1 V F
  obtain ⟨hFs, hFys, hFtot⟩ :=
    globalResidualHom_surface_flag_weights6630 P0 P1 V F hS hYS hTotal
  have hR : Fres.degreeOf (2 : Fin 4) ≤ 8 := by
    have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> rfl
    rw [hw, wt, MvPolynomial.weightedTotalDegree_piSingle] at hFs
    exact hFs
  have hY : Fres.degreeOf (1 : Fin 4) ≤ 40 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans hFys
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ 40 at hw
    norm_num at hw
    omega
  have hZ : Fres.degreeOf (3 : Fin 4) ≤ 617 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw :=
      (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hFtot
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 1 ≤ 617 at hw
    norm_num at hw
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hr := (agreementNumerator_degree_bounds Fres 40 8 617
      (by norm_num) hY hR hZ d coeffs x u0 u1).2.1
    convert hr using 1 <;> ring
  · have hweights : totalYRWeights = residualYSWeights := by
      funext i
      fin_cases i <;> rfl
    have hFyr : MvPolynomial.weightedTotalDegree totalYRWeights Fres ≤ 40 := by
      rw [hweights]
      simpa only [wt] using hFys
    have h := agreementNumerator_totalYR_wt_le Fres 40 d
      (by norm_num) hFyr coeffs x u0 u1
    rw [hweights] at h
    calc
      wt residualYSWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
          1 + 2 * d * (40 - 1) := by simpa only [wt] using h
      _ = 1 + 78 * d := by
        norm_num
        ring
  · have h := agreementNumerator_wt_le_minkowski residualTotalWeights rfl
      Fres 617 (by change 1 ≤ 617; norm_num)
      (by change 2 * 1 ≤ 617; norm_num)
      (by change 1 ≤ 1; norm_num) hFtot d coeffs x u0 u1
    calc
      wt residualTotalWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
          max (residualTotalWeights 1) (residualTotalWeights 3) +
            d * (617 + (617 - residualTotalWeights 2)) := h
      _ = 1 + 1233 * d := by
        change max 1 1 + d * (617 + (617 - 1)) = 1 + 1233 * d
        norm_num
        ring

/-- The mapped score-66.42 agreement cut lies in the exact nested flag used
by the sharp mixed-volume ledger. -/
theorem surfaceMap_globalResidual_agreement_in_flag6630
    (phi : Polynomial K →+* Omega)
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 8)
    (hYS : wt residualYSWeights F ≤ 40)
    (hTotal : wt residualTotalWeights F ≤ 617)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (residualAgreementFlag6630 d)
      (surfaceMap phi
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1)) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi
      (agreementNumerator (globalResidualHom P0 P1 V F)
        d coeffs x u0 u1) he)
  obtain ⟨hR, hYS', hTot⟩ := globalResidual_agreement_weight_bounds6630
    P0 P1 V F hS hYS hTotal d coeffs x u0 u1
  have hqR := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hq).trans hR
  have hqYS :=
    (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS'
  have hqTot :=
    (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTot
  rw [ContactFactorCaps.weight_fin4] at hqYS hqTot
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ 1 + 78 * d at hqYS
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ 1 + 1233 * d at hqTot
  norm_num at hqYS hqTot
  rw [residualAgreementFlag6630_value]
  change q 2 ≤ 15 * d ∧
    q 1 + q 2 ≤ (1 + 63 * d) + 15 * d ∧
    q 1 + q 2 + q 3 ≤ 1155 * d + (1 + 63 * d) + 15 * d
  omega

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research.globalResidualHom_surface_flag_weights6630
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research.globalResidual_agreement_weight_bounds6630
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research.surfaceMap_globalResidual_agreement_in_flag6630
