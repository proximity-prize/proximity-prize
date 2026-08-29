import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactRecursiveGCDResearch
import ProximityPrize.SubmissionLower.ContactStackedParameters6656Research

/-!
# Meet and quotient box transport for the stacked 66.56 construction

Divisor monotonicity transports each coordinate cap independently.  Taking
the appropriate coordinate from each parent gives the first GCD box
`(25*a,598,7)` and the final common box `(25*a,598,6)`.  The four residual
quotients retain the boxes of their respective parent equations.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedBoxTransport6656Research

open ProximityPrize.Benchmark
open ContactInterpolation ContactFactorCaps
open ContactRecursiveGCDResearch
open ContactStackedParameters6656Research

noncomputable section

abbrev GlobalPoly := MvPolynomial (Fin 4) IRSProfile.Field

local instance : GCDMonoid GlobalPoly :=
  UniqueFactorizationMonoid.toGCDMonoid GlobalPoly

theorem gcd12_ne_zero {A B : GlobalPoly} (hA : A ≠ 0) :
    gcd12 A B ≠ 0 :=
  gcd_ne_zero_of_left hA

theorem gcd123_ne_zero {A B C : GlobalPoly} (hA : A ≠ 0) :
    gcd123 A B C ≠ 0 :=
  gcd_ne_zero_of_left (gcd12_ne_zero hA)

theorem quotientA_dvd_left (A B : GlobalPoly) : quotientA A B ∣ A := by
  refine ⟨gcd12 A B, ?_⟩
  simpa only [mul_comm] using a_eq_gcd12_mul_quotientA A B

theorem quotientB_dvd_right (A B : GlobalPoly) : quotientB A B ∣ B := by
  refine ⟨gcd12 A B, ?_⟩
  simpa only [mul_comm] using b_eq_gcd12_mul_quotientB A B

theorem middleQuotient_dvd_gcd12 (A B C : GlobalPoly) :
    middleQuotient A B C ∣ gcd12 A B := by
  refine ⟨gcd123 A B C, ?_⟩
  simpa only [mul_comm] using gcd12_eq_gcd123_mul_middleQuotient A B C

theorem quotientC_dvd_right (A B C : GlobalPoly) : quotientC A B C ∣ C := by
  refine ⟨gcd123 A B C, ?_⟩
  simpa only [mul_comm] using c_eq_gcd123_mul_quotientC A B C

/-- The first GCD takes its contact and slope caps from profile A and its
seed cap from profile B. -/
theorem gcd12_mem_meet_box
    (A B : GlobalPoly) (hA : A ≠ 0) (hB : B ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 5263 7)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 598 14) :
    gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 598 7 := by
  have hfromA := mem_globalCoefficientBox_of_dvd (gcd12 A B) A
    (25 * agreements) w 5263 7 hA (gcd_dvd_left A B) hboxA
  have hfromB := mem_globalCoefficientBox_of_dvd (gcd12 A B) B
    (47 * agreements) w 598 14 hB (gcd_dvd_right A B) hboxB
  intro d hd
  exact ⟨(hfromB hd).1, (hfromA hd).2.1, (hfromA hd).2.2⟩

/-- The final GCD retains the first meet's contact/seed caps and takes the
slope-six cap from profile C. -/
theorem gcd123_mem_meet_box
    (A B C : GlobalPoly) (hA : A ≠ 0) (hC : C ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 598 7)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 579299 6) :
    gcd123 A B C ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 598 6 := by
  have h12 := gcd12_ne_zero (B := B) hA
  have hfrom12 := mem_globalCoefficientBox_of_dvd (gcd123 A B C) (gcd12 A B)
    (25 * agreements) w 598 7 h12 (gcd_dvd_left (gcd12 A B) C) hbox12
  have hfromC := mem_globalCoefficientBox_of_dvd (gcd123 A B C) C
    (27 * agreements) w 579299 6 hC (gcd_dvd_right (gcd12 A B) C) hboxC
  intro d hd
  exact ⟨(hfrom12 hd).1, (hfromC hd).2.1, (hfrom12 hd).2.2⟩

theorem quotientA_mem_parent_box
    (A B : GlobalPoly) (hA : A ≠ 0)
    (hboxA : A ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 5263 7) :
    quotientA A B ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 5263 7 :=
  mem_globalCoefficientBox_of_dvd (quotientA A B) A
    (25 * agreements) w 5263 7 hA (quotientA_dvd_left A B) hboxA

theorem quotientB_mem_parent_box
    (A B : GlobalPoly) (hB : B ≠ 0)
    (hboxB : B ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 598 14) :
    quotientB A B ∈ globalCoefficientBox IRSProfile.Field
      (47 * agreements) w 598 14 :=
  mem_globalCoefficientBox_of_dvd (quotientB A B) B
    (47 * agreements) w 598 14 hB (quotientB_dvd_right A B) hboxB

theorem middleQuotient_mem_parent_box
    (A B C : GlobalPoly) (hA : A ≠ 0)
    (hbox12 : gcd12 A B ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 598 7) :
    middleQuotient A B C ∈ globalCoefficientBox IRSProfile.Field
      (25 * agreements) w 598 7 :=
  mem_globalCoefficientBox_of_dvd (middleQuotient A B C) (gcd12 A B)
    (25 * agreements) w 598 7 (gcd12_ne_zero (B := B) hA)
    (middleQuotient_dvd_gcd12 A B C) hbox12

theorem quotientC_mem_parent_box
    (A B C : GlobalPoly) (hC : C ≠ 0)
    (hboxC : C ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 579299 6) :
    quotientC A B C ∈ globalCoefficientBox IRSProfile.Field
      (27 * agreements) w 579299 6 :=
  mem_globalCoefficientBox_of_dvd (quotientC A B C) C
    (27 * agreements) w 579299 6 hC (quotientC_dvd_right A B C) hboxC

end

end ProximityPrize.SubmissionLower.ContactStackedBoxTransport6656Research
