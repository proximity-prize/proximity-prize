import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedBoxTransport6656Research
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research

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

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

/-- The first GCD takes weighted and slope caps from A and the seed cap from
B. -/
theorem gcd12_mem_meet_box
    (A B : GlobalPoly) (hA : A ≠ 0) (hB : B ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 11937 7)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (34 * agreements) w 1059 9) :
    gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 1059 7 := by
  have hfromA := mem_globalCoefficientBox_of_dvd (gcd12 A B) A
    (27 * agreements) w 11937 7 hA (gcd_dvd_left A B) hboxA
  have hfromB := mem_globalCoefficientBox_of_dvd (gcd12 A B) B
    (34 * agreements) w 1059 9 hB (gcd_dvd_right A B) hboxB
  intro d hd
  exact ⟨(hfromB hd).1, (hfromA hd).2.1, (hfromA hd).2.2⟩

/-- The final GCD retains the first meet's weighted/slope caps and takes the
seed cap from C. -/
theorem gcd123_mem_meet_box
    (A B C : GlobalPoly) (hA : A ≠ 0) (hC : C ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 1059 7)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (54 * agreements) w 690 16) :
    gcd123 A B C ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 690 7 := by
  have h12 :=
    ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA
  have hfrom12 := mem_globalCoefficientBox_of_dvd
    (gcd123 A B C) (gcd12 A B)
    (27 * agreements) w 1059 7 h12
    (gcd_dvd_left (gcd12 A B) C) hbox12
  have hfromC := mem_globalCoefficientBox_of_dvd (gcd123 A B C) C
    (54 * agreements) w 690 16 hC
    (gcd_dvd_right (gcd12 A B) C) hboxC
  intro d hd
  exact ⟨(hfromC hd).1, (hfrom12 hd).2.1, (hfrom12 hd).2.2⟩

theorem quotientA_mem_parent_box
    (A B : GlobalPoly) (hA : A ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 11937 7) :
    quotientA A B ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 11937 7 :=
  mem_globalCoefficientBox_of_dvd (quotientA A B) A
    (27 * agreements) w 11937 7 hA
    (ContactStackedBoxTransport6656Research.quotientA_dvd_left A B) hboxA

theorem quotientB_mem_parent_box
    (A B : GlobalPoly) (hB : B ≠ 0)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (34 * agreements) w 1059 9) :
    quotientB A B ∈ globalCoefficientBox IRSProfile.Field
      (34 * agreements) w 1059 9 :=
  mem_globalCoefficientBox_of_dvd (quotientB A B) B
    (34 * agreements) w 1059 9 hB
    (ContactStackedBoxTransport6656Research.quotientB_dvd_right A B) hboxB

theorem middleQuotient_mem_parent_box
    (A B C : GlobalPoly) (hA : A ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 1059 7) :
    middleQuotient A B C ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 1059 7 :=
  mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
    (27 * agreements) w 1059 7
    (ContactStackedBoxTransport6656Research.gcd12_ne_zero (B := B) hA)
    (ContactStackedBoxTransport6656Research.middleQuotient_dvd_gcd12 A B C)
    hbox12

theorem quotientC_mem_parent_box
    (A B C : GlobalPoly) (hC : C ≠ 0)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (54 * agreements) w 690 16) :
    quotientC A B C ∈ globalCoefficientBox IRSProfile.Field
      (54 * agreements) w 690 16 :=
  mem_globalCoefficientBox_of_dvd (quotientC A B C) C
    (54 * agreements) w 690 16 hC
    (ContactStackedBoxTransport6656Research.quotientC_dvd_right A B C) hboxC

end

end ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research

#print axioms ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research.gcd12_mem_meet_box
#print axioms ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research.gcd123_mem_meet_box
#print axioms ProximityPrize.SubmissionLower.ContactStackedBoxTransport6670Research.middleQuotient_mem_parent_box
