import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
namespace ProximityPrize.SubmissionLower.LocatorArithmetic
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
open RCN100 RCN119 RCN302 RCN318 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80555
def agreements : ℕ := 181589
def gap : ℕ := 50518
def prime : ℕ := 2130706433
def budget : ℕ := 274980725639732053
def LA : ℕ := 127295
def LB : ℕ := 8000
def LCap : ℕ := 3500
def weightedA : ℕ := 12166463
def weightedC : ℕ := 33775554
abbrev weightedAmbient := weightedC
def weightedB : ℕ := 13800764
def weightedTCap : ℕ := 19066845
def fixedRegularCap : ℕ := 266990962477160602
theorem kernelA_rank : localRankBound 67 127295 20 = 4662791042 := by decide
theorem kernelC_rank : localRankBound 186 127295 55 = 94702619396 := by decide
theorem kernelB_rank : localRankBound 76 8000 23 = 426829720 := by decide
theorem kernelTCap_rank : localRankBound 105 3500 32 = 482388049 := by decide
theorem kernelA_nullity :
    coefficientCount 12166463 131071 127295 20 -
      262144 * localRankBound 67 127295 20 = 44903196289 := by
  rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    12166463 131071 127295 20 93 (by decide) (by decide)]
  decide
theorem kernelC_nullity :
    coefficientCount 33775554 131071 127295 55 -
      262144 * localRankBound 186 127295 55 = 138089187217758 := by
  rw [kernelC_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    33775554 131071 127295 55 258 (by decide) (by decide)]
  decide
theorem kernelB_nullity :
    coefficientCount 13800764 131071 8000 23 -
      262144 * localRankBound 76 8000 23 = 12925178954 := by
  rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13800764 131071 8000 23 106 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity :
    coefficientCount 19066845 131071 3500 32 -
      262144 * localRankBound 105 3500 32 = 3751230769 := by
  rw [kernelTCap_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    19066845 131071 3500 32 146 (by decide) (by decide)]
  decide
theorem A_ys85_quotient_upper :
    coefficientCount 171107 131071 127209 19 = 31952527727 := by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    171107 131071 127209 19 2 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt :
    coefficientCount 19066845 131071 2 32 <
    coefficientCount 19066845 131071 3500 32 -
      262144 * localRankBound 105 3500 32 := by
  rw [kernelTCap_nullity]
  decide
def fixedSingular : TightParameters := ⟨n, w, agreements, weightedA, 3500, 20⟩
def residualStage : UnequalParameters := ⟨n, w, agreements, 105, 23, LB, 257, 55, LA⟩
def residualSingular : TightParameters := ⟨n, w, agreements, weightedB, LB, 23⟩
theorem fixedSingular_exact : fixedSingular.countCap = 1008282787015382 := by decide
theorem residualStage_exact : residualStage.regularCountCap = 2172114644764710 := by decide
theorem residualSingular_exact : residualSingular.countCap = 3480606302767085 := by decide
structure SingularGates (P : TightParameters) : Prop where
  s_pos : 1 ≤ P.s
  s_small : P.s < prime
  w_pos : 1 ≤ P.w
  w_small : P.w < prime
  kD : P.w < P.kappa * P.D
  algebraic_pos : 1 ≤ P.algebraicCap
  implicit_small : P.implicitYCap < prime
  algebraic_small : P.algebraicCap < prime
  mixed_small : 2 * P.implicitYCap * P.algebraicCap < prime
  wa : P.w < P.a
  an : P.a ≤ P.n
theorem residual_singular_gates : SingularGates residualSingular := by constructor <;> decide
structure ResidualGates : Prop where
  qY : (residualSingular.D - 1) / w ≤ residualStage.leftY
  qR : residualSingular.s ≤ residualStage.leftR
  qZ : residualSingular.L ≤ residualStage.leftZ
  rightY : (weightedAmbient - 1) / w ≤ residualStage.rightY
  leftR_pos : 1 ≤ residualStage.leftR
  leftY_small : residualStage.leftY < prime
  leftR_small : residualStage.leftR < prime
  leftZ_small : residualStage.leftZ < prime
  mixedY_small : residualStage.mixedCost.y < prime
  mixedR_small : residualStage.mixedCost.r < prime
  mixedZ_small : residualStage.mixedCost.z < prime
theorem residual_gates : ResidualGates := by constructor <;> decide
def ledger : ℕ := fixedRegularCap + fixedSingular.countCap +
  residualStage.regularCountCap + residualSingular.countCap
theorem ledger_exact : ledger = 273651966211707779 := by
  rw [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, residualSingular_exact]
theorem ledger_lt : ledger < budget := by rw [ledger_exact]; decide
def radiusNumerator : ℕ := 10309859
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator
theorem radius_floor :
    ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = 80545 := by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    errors, IRSProfile.Index]
theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_root_integer : (2 : ℕ)^79 * 454^100 ≤ 785^100 := by decide
theorem score_radius_integer :
    (23244573 : ℕ)^128 * (2^67 * 785) ≤ 454 * 33554432^128 := by decide
theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((79 : ℝ) / 100) ≤ (785 : ℝ≥0) / 454 := by
  have hroot : ((2 : ℝ≥0)^(79 : ℕ))^((100 : ℝ)⁻¹) ≤ (785 : ℝ≥0) / 454 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((79 : ℝ) / 100) = ((2 : ℝ≥0)^(79 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot
theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2^(67 : ℕ)) * (454 / 785) := by
  have hsub : (1 - radius : ℝ≥0) = 23244573 / 33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0) / 2^(67 : ℕ)) * (454 / 785)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6779 := by
  have hscale : (454 : ℝ≥0) / 785 ≤ (2 : ℝ≥0)^(-((79 : ℝ) / 100)) := by
    calc
      (454 : ℝ≥0) / 785 = 1 / ((785 : ℝ≥0) / 454) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0)^((79 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2^(67 : ℕ)) * (454 / 785) := radius_power_bound
    _ ≤ ((1 : ℝ≥0) / 2^(67 : ℕ)) * (2 : ℝ≥0)^(-((79 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6779 := by
      unfold claimedError
      rw [show -((((6779 : ℕ) : ℝ) / 100)) =
          -((67 : ℕ) : ℝ) + -((79 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end LocatorArithmetic
