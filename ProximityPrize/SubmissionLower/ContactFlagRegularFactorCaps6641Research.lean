import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactRegularFactorFlag6630Research
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research
import ProximityPrize.SubmissionLower.ContactFlagParameters6641Research

/-!
# Cumulative regular-factor caps from the flag-complete interpolant

The new interpolation box caps `Y+R+Z` directly at 814.  This gives the
`(766,38,10)` surface flag used by the score-66.74 recursive
geometry, despite adding the previously omitted interpolation wedge.
-/

namespace ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6641Research

open scoped Classical BigOperators
open ContactFlagParameters6641Research
open ContactFlagInterpolation6641Research
open ContactRegularFactorFlag6630Research
open ContactSelectedSeedDecomposition ContactImplicitContactLift ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactCumulativeWeightedDegreeResearch

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {K : Type} [Field K]

theorem residual_surface_weights_of_flagBox6641
    (F : MvPolynomial (Fin 4) K)
    (hbox : F ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    MvPolynomial.weightedTotalDegree residualSWeights F ≤ 10 ∧
      MvPolynomial.weightedTotalDegree residualYSWeights F ≤ 48 ∧
      MvPolynomial.weightedTotalDegree residualTotalWeights F ≤ 814 := by
  constructor
  · apply (weightedTotalDegree_le_iff residualSWeights F 10).mpr
    intro d hd
    have hb : d 1 + d 2 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
        d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
    rw [weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 10
    norm_num [slopeCap] at hb ⊢
    exact hb.2.1
  · constructor
    · apply (weightedTotalDegree_le_iff residualYSWeights F 48).mpr
      intro d hd
      have hb : d 1 + d 2 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
          d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
      rw [weight_fin4]
      change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 48
      have hs : d 2 ≤ 10 := by
        simpa only [slopeCap] using hb.2.1
      have hw : d 0 + 131071 * d 1 + 131070 * d 2 < 6392050 := by
        simpa only [ContactFlagParameters6641Research.w,
          ContactFlagParameters6641Research.weightedCap,
          ContactFlagParameters6641Research.multiplicity,
          ContactFlagParameters6641Research.agreements,
          ContactFlagParameters6641Research.n,
          ContactFlagParameters6641Research.errors,
          Nat.reduceSub, Nat.reduceMul] using hb.2.2
      norm_num
      omega
    · apply (weightedTotalDegree_le_iff residualTotalWeights F 814).mpr
      intro d hd
      have hb : d 1 + d 2 + d 3 ≤ seedTotalCap ∧ d 2 ≤ slopeCap ∧
          d 0 + w * d 1 + (w - 1) * d 2 < weightedCap := hbox hd
      rw [weight_fin4]
      change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 814
      norm_num [seedTotalCap] at hb ⊢
      exact hb.1

theorem regularFlag6630_budgets_of_flagBox6641
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap) :
    (∑ F : RegularIndex Q, (regularFlag6630 Q F).all) ≤ 10 ∧
      (∑ F : RegularIndex Q,
        ((regularFlag6630 Q F).yz + (regularFlag6630 Q F).all)) ≤ 48 ∧
      (∑ F : RegularIndex Q,
        ((regularFlag6630 Q F).zOnly + (regularFlag6630 Q F).yz +
          (regularFlag6630 Q F).all)) ≤ 814 := by
  classical
  have hprod := positiveRFactors_product_dvd Q hQ
  have hs := sum_weightedTotalDegree_le_of_prod_dvd residualSWeights
    (positiveRFactors Q) id Q hQ hprod
  have hys := sum_weightedTotalDegree_le_of_prod_dvd residualYSWeights
    (positiveRFactors Q) id Q hQ hprod
  have htotal := sum_weightedTotalDegree_le_of_prod_dvd residualTotalWeights
    (positiveRFactors Q) id Q hQ hprod
  obtain ⟨hQs, hQys, hQtotal⟩ := residual_surface_weights_of_flagBox6641 Q hbox
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

end ProximityPrize.SubmissionLower.ContactFlagRegularFactorCaps6641Research
