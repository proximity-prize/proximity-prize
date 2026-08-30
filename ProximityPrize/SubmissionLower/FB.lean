import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Bx
namespace ProximityPrize.SubmissionLower.ContactMovingSeedless6732Research
open ProximityPrize.Benchmark
open ContactSeedlessInterpolationResearch
open scoped NNReal
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80112
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def prime : ℕ := 2130706433
def multiplicity : ℕ := 42
def yTotalCap : ℕ := 57
def slopeCap : ℕ := 12
def weightedCap : ℕ := multiplicity * agreements
def listBudget : ℕ := 1000000000
def capY : ℕ := 1 + 2*w*yTotalCap
def capR : ℕ := w*(2*slopeCap - 1)
def regularListNumerator : ℕ := (n-w)*(capY*slopeCap + capR*yTotalCap)
def singularListCap : ℕ := (2*slopeCap - 1)*yTotalCap
def listNumerator : ℕ := regularListNumerator + singularListCap*gap
theorem coefficient_count_exact :
   coefficientCount weightedCap w yTotalCap slopeCap = 2389158005 := by decide
theorem local_rank_exact :
   localRankBound multiplicity yTotalCap slopeCap = 9113 := by decide
theorem nullity_exact :
   coefficientCount weightedCap w yTotalCap slopeCap -
     n*localRankBound multiplicity yTotalCap slopeCap = 239733 := by
 rw [coefficient_count_exact, local_rank_exact]
 decide
theorem interpolation_gate :
   n*localRankBound multiplicity yTotalCap slopeCap <
     coefficientCount weightedCap w yTotalCap slopeCap := by
 rw [coefficient_count_exact, local_rank_exact]
 decide
theorem list_numeric_values :
   agreements=182032 ∧ gap=50961 ∧ weightedCap=7645344 ∧
   singularListCap=1311 ∧ listNumerator=46024937924004 ∧
   listNumerator/gap+1=903140400 ∧
   listNumerator<903140400*gap ∧ 903140400<listBudget := by decide
theorem list_numerator_fits : listNumerator < listBudget*gap := by decide
theorem characteristic_gates : 0 < slopeCap ∧ slopeCap < prime ∧ yTotalCap < prime ∧
   (2*slopeCap - 1)*weightedCap < prime ∧ singularListCap < prime := by decide
theorem exists_seedless_interpolant (received : IRSProfile.Index → IRSProfile.Field) :
   ∃ Q : MvPolynomial (Fin 4) IRSProfile.Field,
     Q ≠ 0 ∧ Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w yTotalCap slopeCap ∧
     ∀ (i : IRSProfile.Index) (r : ℕ),
       ContactFlagRankKernel6641Research.slopeDifference IRSProfile.Field ^ (multiplicity-r) ∣
         (ContactTranslation.homogenizedTranslation IRSProfile.Field
           (IRSProfile.domain i) (received i) 0 Q).coeff r := by
 obtain ⟨theta, htheta, hzero⟩ := exists_nonzero_kernel_array
   IRSProfile.Field weightedCap w yTotalCap slopeCap multiplicity
   IRSProfile.domain received (by
     rw [show Fintype.card IRSProfile.Index = n by norm_num [IRSProfile.Index, n]]
     exact interpolation_gate)
 refine ⟨reconstruct IRSProfile.Field weightedCap w yTotalCap slopeCap theta,
   reconstruct_ne_zero IRSProfile.Field _ _ _ _ theta htheta,
   reconstruct_mem_box IRSProfile.Field _ _ _ _ theta, ?_⟩
 intro i r
 have hdiv := all_blocks_divisible_of_kernel IRSProfile.Field
   weightedCap w yTotalCap slopeCap multiplicity IRSProfile.domain received theta hzero i r
 rw [← translation_reconstruct_coeff IRSProfile.Field weightedCap w
   yTotalCap slopeCap (IRSProfile.domain i) (received i) theta r] at hdiv
 exact hdiv
def radius : ℝ≥0 := claimedRadius 10254463 33554432
def score : ℕ := 6735
theorem radius_numerator_exact : 10254463 = 128*errors+127 := by decide
theorem radius_floor :
   ⌊(radius : ℝ)*(Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
 norm_num [radius, claimedRadius, errors, IRSProfile.Index]
theorem radius_cell_cross :
   10254463*Fintype.card IRSProfile.Index < (errors+1)*33554432 := by
 norm_num [IRSProfile.Index, errors]
theorem radius_gap : w < Fintype.card IRSProfile.Index-errors := by
 norm_num [IRSProfile.Index, errors, w]
theorem radius_admissible :
   radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
 constructor <;> norm_num [radius, claimedRadius, IRSProfile.minRelativeDistance]
theorem root_power_integer : (2 : ℕ)^7 * 91^20 ≤ 116^20 := by decide
theorem radius_power_integer :
   (23299969 : ℕ)^128 * (2^67*116) ≤ 91*33554432^128 := by decide
theorem two_rpow_fraction_le :
   (2 : ℝ≥0)^((7 : ℝ)/20) ≤ (116 : ℝ≥0)/91 := by
 have hroot : ((2 : ℝ≥0)^(7 : ℕ))^((20 : ℝ)⁻¹) ≤ (116 : ℝ≥0)/91 := by
   rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ)<20)]
   rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
   exact_mod_cast root_power_integer
 calc
   (2 : ℝ≥0)^((7 : ℝ)/20)=((2 : ℝ≥0)^(7 : ℕ))^((20 : ℝ)⁻¹) := by
     rw [← NNReal.rpow_natCast_mul]
     norm_num [div_eq_mul_inv]
   _ ≤ (116 : ℝ≥0)/91 := hroot
theorem radius_power_rational_bound :
   (1-radius)^IRSProfile.repetitions ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(91/116) := by
 have hsub : (1-radius : ℝ≥0)=23299969/33554432 := by
   have hr : radius≤1 := by
     rw [← NNReal.coe_le_coe]
     norm_num [radius,claimedRadius]
   apply NNReal.coe_injective
   rw [NNReal.coe_sub hr]
   norm_num [radius,claimedRadius]
 have hpow : ((23299969 : ℝ≥0)/33554432)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ))*(91/116) := by
   rw [div_pow, show ((1 : ℝ≥0)/2^(67 : ℕ))*(91/116) =
     (91 : ℝ≥0)/(2^67*116) by ring]
   rw [div_le_div_iff₀ (by positivity) (by positivity)]
   exact_mod_cast radius_power_integer
 simpa only [IRSProfile.repetitions,hsub] using hpow
theorem score_target_le :
   (1-radius)^IRSProfile.repetitions ≤ claimedError 6735 := by
 have htwo : (1 : ℝ≥0)/2^(67 : ℕ)*(91/116) ≤ claimedError 6735 := by
   rw [claimedError,show ((((6735 : ℕ) : ℝ)/100))=67+((7 : ℝ)/20) by norm_num,
     show -(67 + ((7 : ℝ) / 20)) = -(67 : ℝ) + -((7 : ℝ) / 20) by ring,
     NNReal.rpow_add two_ne_zero,NNReal.rpow_neg,NNReal.rpow_neg,one_div]
   have hfrac : (91 : ℝ≥0)/116 ≤ ((2 : ℝ≥0)^((7 : ℝ)/20))⁻¹ := by
     apply (le_inv_comm₀ (by positivity) (by positivity)).2
     simpa using two_rpow_fraction_le
   simpa [NNReal.rpow_natCast] using
     (mul_le_mul_right hfrac (((2 : ℝ≥0) ^ (67 : ℝ))⁻¹))
 exact radius_power_rational_bound.trans htwo
end
end ProximityPrize.SubmissionLower.ContactMovingSeedless6732Research
