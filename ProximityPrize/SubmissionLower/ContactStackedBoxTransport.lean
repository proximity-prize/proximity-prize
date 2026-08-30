import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactRecursiveGCD
import ProximityPrize.SubmissionLower.ContactStackedParameters

namespace ProximityPrize.SubmissionLower.ContactStackedBoxTransport

open ProximityPrize.Benchmark
open ContactInterpolation ContactFactorCaps
open ContactRecursiveGCD
open ContactStackedParameters

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

end

end ProximityPrize.SubmissionLower.ContactStackedBoxTransport
