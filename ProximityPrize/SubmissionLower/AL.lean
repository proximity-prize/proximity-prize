import ProximityPrize.SubmissionLower.CJ
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.D1
import ProximityPrize.SubmissionLower.Z8
namespace ProximityPrize.SubmissionLower.ContactTwoTailParameters6734Research
open ProximityPrize.Benchmark
open ContactFlagBezout6543Research
open ContactResidualSupportParametersResearch
open ContactMovingAgreementCertificate6719Research
open ContactMovingPositiveLedger6719Research
open ContactReducedTaylorProfileResearch
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def score : ℕ := 6735
def errors : ℕ := 80112
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def radiusNumerator : ℕ := 10254463
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
structure Profile where
 multiplicity : ℕ
 totalCap : ℕ
 slopeCap : ℕ
 middleCap : ℕ
 deriving DecidableEq
namespace Profile
def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
end Profile
def profileA : Profile := ⟨42,84439,12,58⟩
def profileB : Profile := ⟨81,1284,25,112⟩
def profileC : Profile := ⟨42,13754,12,58⟩
def capacity : ℕ := prime ^ 6 / 2 ^ 128
def listBudget : ℕ := 1000000000
def mcaBudget : ℕ := capacity - listBudget
theorem basic_values :
   agreements = 182032 ∧ gap = 50961 ∧
     profileA.weightedCap = 7645344 ∧
     profileB.weightedCap = 14744592 ∧
     profileC.weightedCap = 7645344 := by
 decide
theorem budget_values :
   capacity = 274980728111395087 ∧
     mcaBudget = 274980727111395087 := by
 decide
theorem radius_floor :
   ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
 norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
   errors, IRSProfile.Index]
theorem radius_admissible :
   radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
 constructor <;>
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
     IRSProfile.minRelativeDistance]
theorem score_root_integer : (2 : ℕ) ^ 7 * 91 ^ 20 ≤ 116 ^ 20 := by
 decide
theorem score_radius_integer :
   (23299969 : ℕ) ^ 128 * (2 ^ 67 * 116) ≤ 91 * 33554432 ^ 128 := by
 decide
theorem two_rpow_score_fraction_le :
   (2 : ℝ≥0) ^ ((7 : ℝ) / 20) ≤ (116 : ℝ≥0) / 91 := by
 have hroot : ((2 : ℝ≥0) ^ (7 : ℕ)) ^ ((20 : ℝ)⁻¹) ≤
     (116 : ℝ≥0) / 91 := by
   rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 20)]
   rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
   exact_mod_cast score_root_integer
 calc
   (2 : ℝ≥0) ^ ((7 : ℝ) / 20) =
       ((2 : ℝ≥0) ^ (7 : ℕ)) ^ ((20 : ℝ)⁻¹) := by
     rw [← NNReal.rpow_natCast_mul]
     norm_num [div_eq_mul_inv]
   _ ≤ (116 : ℝ≥0) / 91 := hroot
theorem radius_power_rational_bound :
   (1 - radius) ^ IRSProfile.repetitions ≤
     ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) * (91 / 116) := by
 have hsub : (1 - radius : ℝ≥0) = 23299969 / 33554432 := by
   have hr : radius ≤ 1 := by
     rw [← NNReal.coe_le_coe]
     norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
   apply NNReal.coe_injective
   rw [NNReal.coe_sub hr]
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
 change (1 - radius) ^ 128 ≤ ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) * (91 / 116)
 rw [hsub, div_pow, div_mul_div_comm, one_mul,
   div_le_div_iff₀ (by positivity) (by positivity)]
 exact_mod_cast score_radius_integer
theorem score_target_le :
   (1 - radius) ^ IRSProfile.repetitions ≤ claimedError score := by
 have hscale : (91 : ℝ≥0) / 116 ≤
     (2 : ℝ≥0) ^ (-((7 : ℝ) / 20)) := by
   calc
     (91 : ℝ≥0) / 116 = 1 / ((116 : ℝ≥0) / 91) := by norm_num
     _ ≤ 1 / ((2 : ℝ≥0) ^ ((7 : ℝ) / 20)) :=
       one_div_le_one_div_of_le (by positivity) two_rpow_score_fraction_le
     _ = (2 : ℝ≥0) ^ (-((7 : ℝ) / 20)) := by
       rw [one_div, NNReal.rpow_neg]
 calc
   (1 - radius) ^ IRSProfile.repetitions ≤
       ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) * (91 / 116) :=
     radius_power_rational_bound
   _ ≤ ((1 : ℝ≥0) / 2 ^ (67 : ℕ)) *
       (2 : ℝ≥0) ^ (-((7 : ℝ) / 20)) :=
     mul_le_mul_of_nonneg_left hscale (by positivity)
   _ = claimedError score := by
     unfold claimedError score
     rw [show -((((6735 : ℕ) : ℝ) / 100)) =
         -((67 : ℕ) : ℝ) + -((7 : ℝ) / 20) by norm_num,
       NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
     simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.ContactTwoTailParameters6734Research
