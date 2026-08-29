import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6656Research
import ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactResidualSupportParametersResearch
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research

namespace ProximityPrize.SubmissionLower.ContactMovingStackedBoxTransport6732Research

open ProximityPrize.Benchmark
open ContactInterpolation ContactFactorCaps ContactRecursiveGCDResearch
open ContactMovingParameters6732Research
attribute [local simp] n errors agreements
open ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

def fixedSupport : ResidualSupportParameters :=
  ⟨12, 55, 1340, by decide, by decide, by decide, by decide⟩

local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

theorem gcd12_mem_meet_box
    (A B : GlobalPoly) (hA : A ≠ 0) (hB : B ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 20000 12)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1340 22) :
    gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 1340 12 := by
  have hfromA := mem_globalCoefficientBox_of_dvd (gcd12 A B) A
    (47 * agreements) w 20000 12 hA (gcd_dvd_left A B) hboxA
  have hfromB := mem_globalCoefficientBox_of_dvd (gcd12 A B) B
    (76 * agreements) w 1340 22 hB (gcd_dvd_right A B) hboxB
  intro d hd
  exact ⟨(hfromB hd).1, (hfromA hd).2.1, (hfromA hd).2.2⟩

theorem gcd123_mem_meet_box
    (A B C : GlobalPoly) (hA : A ≠ 0) (hC : C ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 1340 12)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (48 * agreements) w 20000 12) :
    gcd123 A B C ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 1340 12 := by
  have h12 :=
    ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA
  have hfrom12 := mem_globalCoefficientBox_of_dvd
    (gcd123 A B C) (gcd12 A B)
    (47 * agreements) w 1340 12 h12
    (gcd_dvd_left (gcd12 A B) C) hbox12
  have hfromC := mem_globalCoefficientBox_of_dvd (gcd123 A B C) C
    (48 * agreements) w 20000 12 hC
    (gcd_dvd_right (gcd12 A B) C) hboxC
  intro d hd
  exact ⟨(hfrom12 hd).1, (hfrom12 hd).2.1, (hfromC hd).2.2⟩

theorem quotientA_mem_parent_box
    (A B : GlobalPoly) (hA : A ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 20000 12) :
    quotientA A B ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 20000 12 :=
  mem_globalCoefficientBox_of_dvd (quotientA A B) A
    (47 * agreements) w 20000 12 hA
    (ContactStackedBoxTransport6656Research.quotientA_dvd_left A B) hboxA

theorem quotientB_mem_parent_box
    (A B : GlobalPoly) (hB : B ≠ 0)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1340 22) :
    quotientB A B ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1340 22 :=
  mem_globalCoefficientBox_of_dvd (quotientB A B) B
    (76 * agreements) w 1340 22 hB
    (ContactStackedBoxTransport6656Research.quotientB_dvd_right A B) hboxB

theorem middleQuotient_mem_parent_box
    (A B C : GlobalPoly) (hA : A ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 1340 12) :
    middleQuotient A B C ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 1340 12 :=
  mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
    (47 * agreements) w 1340 12
    (ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA)
    (ContactStackedBoxTransport6656Research.middleQuotient_dvd_gcd12 A B C)
    hbox12

theorem quotientC_mem_parent_box
    (A B C : GlobalPoly) (hC : C ≠ 0)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (48 * agreements) w 20000 12) :
    quotientC A B C ∈ globalCoefficientBox IRSProfile.Field
      (48 * agreements) w 20000 12 :=
  mem_globalCoefficientBox_of_dvd (quotientC A B C) C
    (48 * agreements) w 20000 12 hC
    (ContactStackedBoxTransport6656Research.quotientC_dvd_right A B C) hboxC

theorem gcd123_support_of_flagB
    (A B C : GlobalPoly) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 20000 12)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (76 * agreements) w 1340 22)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (48 * agreements) w 20000 12)
    (hflagB : B ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field (76 * agreements) w 1340 22) :
    ResidualSupportData fixedSupport (gcd123 A B C) := by
  have hbox := gcd123_mem_meet_box A B C hA hC
    (gcd12_mem_meet_box A B hA hB hboxA hboxB) hboxC
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights (gcd123 A B C) 12).mpr
    intro d hd
    have hb := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 12
    simpa using hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights (gcd123 A B C) 55).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 1340 ∧ d 2 ≤ 12 ∧
        d 0 + 131071 * d 1 + 131070 * d 2 < 8555504 := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 55
    norm_num [agreements, w] at hb ⊢
    omega
  · have hBtotal : wt residualTotalWeights B ≤ 1340 := by
      apply (weightedTotalDegree_le_iff residualTotalWeights B 1340).mpr
      intro d hd
      have hb := hflagB hd
      rw [ContactFactorCaps.weight_fin4]
      change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 1340
      simpa using hb.1
    have hdiv : gcd123 A B C ∣ B :=
      (gcd_dvd_left (gcd12 A B) C).trans (gcd_dvd_right A B)
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (gcd123 A B C) B hdiv hB).trans hBtotal

end

end ProximityPrize.SubmissionLower.ContactMovingStackedBoxTransport6732Research
