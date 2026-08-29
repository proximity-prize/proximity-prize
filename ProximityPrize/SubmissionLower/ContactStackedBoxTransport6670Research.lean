import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6656Research
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactFixedMeetProfile6670Research
import ProximityPrize.SubmissionLower.ContactFlagInterpolation6641Research

/-!
# Meet and quotient box transport for the stacked 67.30 construction

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
      (50 * agreements) w 25000 15)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (60 * agreements) w 3100 18) :
    gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 540 8 := by
  have hfromA := mem_globalCoefficientBox_of_dvd (gcd12 A B) A
    (50 * agreements) w 25000 15 hA (gcd_dvd_left A B) hboxA
  have hfromB := mem_globalCoefficientBox_of_dvd (gcd12 A B) B
    (60 * agreements) w 3100 18 hB (gcd_dvd_right A B) hboxB
  intro d hd
  exact ⟨(hfromB hd).1, (hfromA hd).2.1, (hfromA hd).2.2⟩

/-- The final GCD retains the first meet's weighted/seed caps and takes the
slope cap from C. -/
theorem gcd123_mem_meet_box
    (A B C : GlobalPoly) (hA : A ≠ 0) (hC : C ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 540 8)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 800000 15) :
    gcd123 A B C ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 540 8 := by
  have h12 :=
    ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA
  have hfrom12 := mem_globalCoefficientBox_of_dvd
    (gcd123 A B C) (gcd12 A B)
    (50 * agreements) w 540 8 h12
    (gcd_dvd_left (gcd12 A B) C) hbox12
  have hfromC := mem_globalCoefficientBox_of_dvd (gcd123 A B C) C
    (50 * agreements) w 800000 15 hC
    (gcd_dvd_right (gcd12 A B) C) hboxC
  intro d hd
  exact ⟨(hfrom12 hd).1, (hfromC hd).2.1, (hfrom12 hd).2.2⟩

theorem quotientA_mem_parent_box
    (A B : GlobalPoly) (hA : A ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 25000 15) :
    quotientA A B ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 25000 15 :=
  mem_globalCoefficientBox_of_dvd (quotientA A B) A
    (50 * agreements) w 25000 15 hA
    (ContactStackedBoxTransport6656Research.quotientA_dvd_left A B) hboxA

theorem quotientB_mem_parent_box
    (A B : GlobalPoly) (hB : B ≠ 0)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (60 * agreements) w 3100 18) :
    quotientB A B ∈ globalCoefficientBox IRSProfile.Field
      (60 * agreements) w 3100 18 :=
  mem_globalCoefficientBox_of_dvd (quotientB A B) B
    (60 * agreements) w 3100 18 hB
    (ContactStackedBoxTransport6656Research.quotientB_dvd_right A B) hboxB

theorem middleQuotient_mem_parent_box
    (A B C : GlobalPoly) (hA : A ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 540 8) :
    middleQuotient A B C ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 540 8 :=
  mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
    (50 * agreements) w 540 8
    (ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA)
    (ContactStackedBoxTransport6656Research.middleQuotient_dvd_gcd12 A B C)
    hbox12

theorem quotientC_mem_parent_box
    (A B C : GlobalPoly) (hC : C ≠ 0)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 800000 15) :
    quotientC A B C ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 800000 15 :=
  mem_globalCoefficientBox_of_dvd (quotientC A B C) C
    (50 * agreements) w 800000 15 hC
    (ContactStackedBoxTransport6656Research.quotientC_dvd_right A B C) hboxC

/-- The joint total cap is inherited from B, not inferred from a rectangle. -/
theorem gcd123_support_of_flagB
    (A B C : GlobalPoly) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 25000 15)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (60 * agreements) w 3100 18)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (50 * agreements) w 800000 15)
    (hflagB : B ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      IRSProfile.Field (60 * agreements) w 3100 18) :
    ResidualSupportData ContactFixedMeetProfile6670Research.fixedSupport
      (gcd123 A B C) := by
  have hbox := gcd123_mem_meet_box A B C hA hC
    (gcd12_mem_meet_box A B hA hB hboxA hboxB) hboxC
  refine ⟨?_, ?_, ?_⟩
  · apply (weightedTotalDegree_le_iff residualSWeights (gcd123 A B C) 8).mpr
    intro d hd
    have hb := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤ 8
    simpa using hb.2.1
  · apply (weightedTotalDegree_le_iff residualYSWeights (gcd123 A B C) 69).mpr
    intro d hd
    have hb := hbox hd
    rw [ContactFactorCaps.weight_fin4]
    change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤ 69
    norm_num [agreements, w] at hb ⊢
    omega
  · have hBtotal : wt residualTotalWeights B ≤ 3100 := by
      apply (weightedTotalDegree_le_iff residualTotalWeights B 3100).mpr
      intro d hd
      have hb := hflagB hd
      rw [ContactFactorCaps.weight_fin4]
      change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤ 3100
      simpa using hb.1
    have hdiv : gcd123 A B C ∣ B :=
      (gcd_dvd_left (gcd12 A B) C).trans (gcd_dvd_right A B)
    exact (weightedTotalDegree_le_of_dvd residualTotalWeights
      (gcd123 A B C) B hdiv hB).trans hBtotal

end

end ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research
