import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6656Research
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research

/-!
# Meet and quotient box transport for the stacked 66.70 construction

The generic divisor identities and divisor-monotonicity theorem are reused
from the accepted stacked construction.  This file contains only the new
coordinatewise target caps.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research

open ProximityPrize.Benchmark
open ContactInterpolation ContactFactorCaps
open ContactRecursiveGCDResearch
open ContactStackedParameters6670Research
open ContactResidualSupportParametersResearch
open ContactIdentityResidualGlobalFlagResearch
open ContactPost6464MinkowskiRecurrenceResearch

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

/-- The first GCD takes weighted and slope caps from A and the seed cap from
B. -/
theorem gcd12_mem_meet_box
    (A B : GlobalPoly) (hA : A ≠ 0) (hB : B ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 20000 10)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (68 * agreements) w 900 21) :
    gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 900 10 := by
  have hfromA := mem_globalCoefficientBox_of_dvd (gcd12 A B) A
    (35 * agreements) w 20000 10 hA (gcd_dvd_left A B) hboxA
  have hfromB := mem_globalCoefficientBox_of_dvd (gcd12 A B) B
    (68 * agreements) w 900 21 hB (gcd_dvd_right A B) hboxB
  intro d hd
  exact ⟨(hfromB hd).1, (hfromA hd).2.1, (hfromA hd).2.2⟩

/-- The final GCD retains the first meet's weighted/seed caps and takes the
slope cap from C. -/
theorem gcd123_mem_meet_box
    (A B C : GlobalPoly) (hA : A ≠ 0) (hC : C ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 900 10)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (38 * agreements) w 42000 10) :
    gcd123 A B C ∈ globalCoefficientBox IRSProfile.Field
      (34 * agreements) w 900 9 := by
  have h12 :=
    ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA
  have hfrom12 := mem_globalCoefficientBox_of_dvd
    (gcd123 A B C) (gcd12 A B)
    (35 * agreements) w 900 10 h12
    (gcd_dvd_left (gcd12 A B) C) hbox12
  have hfromC := mem_globalCoefficientBox_of_dvd (gcd123 A B C) C
    (38 * agreements) w 42000 10 hC
    (gcd_dvd_right (gcd12 A B) C) hboxC
  intro d hd
  have h1 := (hfrom12 hd).1
  have h21 : d 2 ≤ 9 := by
    have hC2 := (hfromC hd).2.1
    have h122 := (hfrom12 hd).2.1
    omega
  have h22 : d 0 + w * d 1 + (w - 1) * d 2 < 34 * agreements := by
    have hd12 := (hfrom12 hd).2.2
    have hdC := (hfromC hd).2.2
    norm_num [agreements, w] at hd12 hdC ⊢
    omega
  exact ⟨h1, h21, h22⟩

theorem quotientA_mem_parent_box
    (A B : GlobalPoly) (hA : A ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 20000 10) :
    quotientA A B ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 20000 10 :=
  mem_globalCoefficientBox_of_dvd (quotientA A B) A
    (35 * agreements) w 20000 10 hA
    (ContactStackedBoxTransport6656Research.quotientA_dvd_left A B) hboxA

theorem quotientB_mem_parent_box
    (A B : GlobalPoly) (hB : B ≠ 0)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (68 * agreements) w 900 21) :
    quotientB A B ∈ globalCoefficientBox IRSProfile.Field
      (68 * agreements) w 900 21 :=
  mem_globalCoefficientBox_of_dvd (quotientB A B) B
    (68 * agreements) w 900 21 hB
    (ContactStackedBoxTransport6656Research.quotientB_dvd_right A B) hboxB

theorem middleQuotient_mem_parent_box
    (A B C : GlobalPoly) (hA : A ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 900 10) :
    middleQuotient A B C ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 900 10 :=
  mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
    (35 * agreements) w 900 10
    (ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA)
    (ContactStackedBoxTransport6656Research.middleQuotient_dvd_gcd12 A B C)
    hbox12

theorem quotientC_mem_parent_box
    (A B C : GlobalPoly) (hC : C ≠ 0)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (38 * agreements) w 42000 10) :
    quotientC A B C ∈ globalCoefficientBox IRSProfile.Field
      (38 * agreements) w 42000 10 :=
  mem_globalCoefficientBox_of_dvd (quotientC A B C) C
    (38 * agreements) w 42000 10 hC
    (ContactStackedBoxTransport6656Research.quotientC_dvd_right A B C) hboxC

/-- The joint total cap is inherited from B, not inferred from a rectangle. -/
theorem gcd123_support_of_flagB
    (A B C : GlobalPoly) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (35 * agreements) w 20000 10)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (68 * agreements) w 900 21)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (38 * agreements) w 42000 10)
    (hflagB : B ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field (68 * agreements) w 900 21) :
    ResidualSupportData ContactFixedMeetProfile6670Research.fixedSupport
      (gcd123 A B C) := by
  have hbox := gcd123_mem_meet_box A B C hA hC
    (gcd12_mem_meet_box A B hA hB hboxA hboxB) hboxC
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights (gcd123 A B C) 9).mpr
    intro d hd
    have hb := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 9
    simpa using hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights (gcd123 A B C) 47).mpr
    intro d hd
    have hb : d 1 + d 3 ≤ 900 ∧ d 2 ≤ 9 ∧
        d 0 + 131071 * d 1 + 131070 * d 2 < 34 * agreements := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 47
    norm_num [agreements, w] at hb ⊢
    omega
  · have hBtotal : wt residualTotalWeights B ≤ 900 := by
      apply (weightedTotalDegree_le_iff residualTotalWeights B 900).mpr
      intro d hd
      have hb := hflagB hd
      rw [ContactFactorCaps.weight_fin4]
      change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 900
      simpa using hb.1
    have hdiv : gcd123 A B C ∣ B :=
      (gcd_dvd_left (gcd12 A B) C).trans (gcd_dvd_right A B)
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (gcd123 A B C) B hdiv hB).trans hBtotal

end

end ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research
