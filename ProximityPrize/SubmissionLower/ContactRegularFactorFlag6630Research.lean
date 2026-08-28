import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSelectedSeedDecomposition
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactCumulativeWeightedDegreeResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch

/-!
# Actual cumulative nested flags for the score-66.30 factors

The old rectangular factor ledger separately summed `deg Y`, `deg R`, and
`deg Z`.  The 66.30 surface is instead controlled by the nested Newton
functionals

* `R`,
* `Y + R`, and
* `Y + R + Z`.

Weighted total degree is additive on a product of nonzero factors.  Thus the
product-divisibility certificate for `positiveRFactors` transfers the exact
surface caps `(8, 40, 609)` to the whole factor family, with no rectangular
overcount.
-/

namespace ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research

open scoped BigOperators
open ContactSelectedSeedDecomposition ContactImplicitContactLift
open ContactInterpolation ContactGenericSurface ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactCumulativeWeightedDegreeResearch
open ContactFlagBezout6543Research
open ContactNearPencil6630FlagResearch

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev RegularIndex (Q : MvPolynomial (Fin 4) K) :=
  ↥(positiveRFactors Q)

/-- The three nested support functionals are genuinely nested, for every
polynomial (not merely for the interpolation polynomial). -/
theorem residual_weight_nested (F : MvPolynomial (Fin 4) K) :
    MvPolynomial.weightedTotalDegree residualSWeights F ≤
        MvPolynomial.weightedTotalDegree residualYSWeights F ∧
      MvPolynomial.weightedTotalDegree residualYSWeights F ≤
        MvPolynomial.weightedTotalDegree residualTotalWeights F := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights F _).mpr
    intro d hd
    have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
    rw [weight_fin4] at h ⊢
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ _
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ _ at h
    norm_num at h ⊢
    omega
  · apply (weightedTotalDegree_le_iff residualYSWeights F _).mpr
    intro d hd
    have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
    rw [weight_fin4] at h ⊢
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ _
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ _ at h
    norm_num at h ⊢
    omega

/-- Exact nested-increment flag of an actual positive-`R` factor. -/
def regularFlag6630 (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) :
    FlagDegree :=
  let inner := MvPolynomial.weightedTotalDegree residualSWeights F.1
  let middle := MvPolynomial.weightedTotalDegree residualYSWeights F.1
  let total := MvPolynomial.weightedTotalDegree residualTotalWeights F.1
  ⟨total - middle, middle - inner, inner⟩

theorem regularFlag6630_cumulative (Q : MvPolynomial (Fin 4) K)
    (F : RegularIndex Q) :
    (regularFlag6630 Q F).all =
        MvPolynomial.weightedTotalDegree residualSWeights F.1 ∧
      (regularFlag6630 Q F).yz + (regularFlag6630 Q F).all =
        MvPolynomial.weightedTotalDegree residualYSWeights F.1 ∧
      (regularFlag6630 Q F).zOnly + (regularFlag6630 Q F).yz +
          (regularFlag6630 Q F).all =
        MvPolynomial.weightedTotalDegree residualTotalWeights F.1 := by
  have hn := residual_weight_nested F.1
  refine ⟨rfl, ?_, ?_⟩
  · exact Nat.sub_add_cancel hn.1
  · simp only [regularFlag6630]
    rw [Nat.add_assoc, Nat.sub_add_cancel hn.1,
      Nat.sub_add_cancel hn.2]

/-- Removing the coefficient variable `X` sends every support exponent into
the exact nested flag of its original factor. -/
theorem surfaceMap_in_regularFlag6630
    (phi : Polynomial K →+* Omega)
    (Q : MvPolynomial (Fin 4) K) (F : RegularIndex Q) :
    PolynomialInFlag (regularFlag6630 Q F) (surfaceMap phi F.1) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi F.1 he)
  have hn := residual_weight_nested F.1
  have hs := MvPolynomial.le_weightedTotalDegree residualSWeights hq
  have hys := MvPolynomial.le_weightedTotalDegree residualYSWeights hq
  have htotal := MvPolynomial.le_weightedTotalDegree residualTotalWeights hq
  rw [weight_fin4] at hs hys htotal
  change q 0 * 0 + q 1 * 0 + q 2 * 1 + q 3 * 0 ≤ _ at hs
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ _ at hys
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ _ at htotal
  norm_num at hs hys htotal
  change q 2 ≤ (regularFlag6630 Q F).all ∧
    q 1 + q 2 ≤ (regularFlag6630 Q F).yz + (regularFlag6630 Q F).all ∧
    q 1 + q 2 + q 3 ≤
      (regularFlag6630 Q F).zOnly + (regularFlag6630 Q F).yz +
        (regularFlag6630 Q F).all
  have hc := regularFlag6630_cumulative Q F
  refine ⟨?_, ?_, ?_⟩
  · rwa [hc.1]
  · rwa [hc.2.1]
  · rwa [hc.2.2]

/-- Exact 66.30 support caps of the reconstructed interpolation polynomial.
This statement is intentionally expressed only through the generic
coefficient box, so the factor theorem has no dependency on a protocol
closure module. -/
theorem residual_surface_weights_of_box6630
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K 5309030 131071 601 8) :
    MvPolynomial.weightedTotalDegree residualSWeights F ≤ 8 ∧
      MvPolynomial.weightedTotalDegree residualYSWeights F ≤ 40 ∧
      MvPolynomial.weightedTotalDegree residualTotalWeights F ≤ 609 := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights F 8).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 601 ∧ d 2 ≤ 8 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5309030 := hbox hd
    rw [weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 8
    norm_num
    exact hb.2.1
  · constructor
    · apply (weightedTotalDegree_le_iff residualYSWeights F 40).mpr
      intro d hd
      have hb : d 1 + d 3 ≤ 601 ∧ d 2 ≤ 8 ∧
          d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5309030 := hbox hd
      rw [weight_fin4]
      change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 40
      norm_num
      omega
    · apply (weightedTotalDegree_le_iff residualTotalWeights F 609).mpr
      intro d hd
      have hb : d 1 + d 3 ≤ 601 ∧ d 2 ≤ 8 ∧
          d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 5309030 := hbox hd
      rw [weight_fin4]
      change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 609
      norm_num
      omega

/-- Product divisibility, rather than three separate rectangular degree
sums, gives the sharp cumulative family flag `(609,40,8)`. -/
theorem regularFlag6630_budgets
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K 5309030 131071 601 8) :
    (∑ F : RegularIndex Q, (regularFlag6630 Q F).all) ≤ 8 ∧
      (∑ F : RegularIndex Q,
        ((regularFlag6630 Q F).yz + (regularFlag6630 Q F).all)) ≤ 40 ∧
      (∑ F : RegularIndex Q,
        ((regularFlag6630 Q F).zOnly + (regularFlag6630 Q F).yz +
          (regularFlag6630 Q F).all)) ≤ 609 := by
  classical
  have hprod := positiveRFactors_product_dvd Q hQ
  have hs := sum_weightedTotalDegree_le_of_prod_dvd residualSWeights
    (positiveRFactors Q) id Q hQ hprod
  have hys := sum_weightedTotalDegree_le_of_prod_dvd residualYSWeights
    (positiveRFactors Q) id Q hQ hprod
  have htotal := sum_weightedTotalDegree_le_of_prod_dvd residualTotalWeights
    (positiveRFactors Q) id Q hQ hprod
  obtain ⟨hQs, hQys, hQtotal⟩ := residual_surface_weights_of_box6630 Q hbox
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl (fun F _ ↦ (regularFlag6630_cumulative Q F).1),
      Finset.sum_coe_sort]
    exact hs.trans hQs
  · rw [Finset.sum_congr rfl (fun F _ ↦
        (regularFlag6630_cumulative Q F).2.1), Finset.sum_coe_sort]
    exact hys.trans hQys
  · rw [Finset.sum_congr rfl (fun F _ ↦
        (regularFlag6630_cumulative Q F).2.2), Finset.sum_coe_sort]
    exact htotal.trans hQtotal

end

end ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research

#print axioms ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research.surfaceMap_in_regularFlag6630
#print axioms ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research.regularFlag6630_budgets
