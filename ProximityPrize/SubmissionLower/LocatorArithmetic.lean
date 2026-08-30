import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1

namespace ProximityPrize.SubmissionLower.LocatorArithmetic
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
open RCN100 RCN119 RCN302
open RCN318 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80201
def agreements : ℕ := 181943
def gap : ℕ := 50872
def prime : ℕ := 2130706433
def budget : ℕ := 274980727043561565
def LA : ℕ := 103470
def LB : ℕ := 1510
def weightedA : ℕ := 13463782
def weightedAux : ℕ := 12008238
def weightedC : ℕ := 8187435
def weightedB : ℕ := 16192927
def fixedRegularCap : ℕ := 250000000000000000

theorem row_values : agreements + errors = n ∧ agreements - w = gap ∧
    weightedA = 74 * agreements ∧ weightedAux = 66 * agreements ∧
    weightedC = 45 * agreements ∧ weightedB = 89 * agreements ∧ w < agreements ∧
    w + 1 ≤ weightedC ∧ weightedA < prime := by decide

theorem kernelA_rank : localRankBound 74 103470 21 = 4889244943 := by decide
theorem kernelAux_rank : localRankBound 66 100000 19 = 3414052680 := by decide
theorem kernelC_rank : localRankBound 45 43759 13 = 490505659 := by decide
theorem kernelB_rank : localRankBound 89 1510 28 = 129058265 := by decide

theorem kernelA_nullity :
    coefficientCount 13463782 131071 103470 21 -
      262144 * localRankBound 74 103470 21 = 6368457832924 := by
  rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13463782 131071 103470 21 103 (by decide) (by decide)]
  decide
theorem kernelAux_nullity :
    coefficientCount 12008238 131071 100000 19 -
      262144 * localRankBound 66 100000 19 = 3688325558435 := by
  rw [kernelAux_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    12008238 131071 100000 19 92 (by decide) (by decide)]
  decide
theorem kernelC_nullity :
    coefficientCount 8187435 131071 43759 13 -
      262144 * localRankBound 45 43759 13 = 9593123806 := by
  rw [kernelC_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    8187435 131071 43759 13 63 (by decide) (by decide)]
  decide
theorem kernelB_nullity :
    coefficientCount 16192927 131071 1510 28 -
      262144 * localRankBound 89 1510 28 = 1995390095 := by
  rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    16192927 131071 1510 28 124 (by decide) (by decide)]
  decide

def fixedSingular : TightParameters := ⟨n, w, agreements, weightedC, 1510, 13⟩
def residualStage : UnequalParameters := ⟨n, w, agreements, 123, 28, LB, 102, 21, LA⟩
def residualSingular : TightParameters := ⟨n, w, agreements, weightedB, LB, 28⟩

theorem fixedSingular_exact : fixedSingular.countCap = 119405126260795 := by decide
theorem residualStage_exact : residualStage.regularCountCap = 862673002713486 := by decide
theorem residualSingular_exact : residualSingular.countCap = 1143307144445833 := by decide

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

theorem fixed_singular_gates : SingularGates fixedSingular := by constructor <;> decide
theorem residual_singular_gates : SingularGates residualSingular := by constructor <;> decide

structure ResidualGates : Prop where
  qY : (residualSingular.D - 1) / w ≤ residualStage.leftY
  qR : residualSingular.s ≤ residualStage.leftR
  qZ : residualSingular.L ≤ residualStage.leftZ
  rightY : (weightedA - 1) / w ≤ residualStage.rightY
  leftR_pos : 1 ≤ residualStage.leftR
  leftY_small : residualStage.leftY < prime
  leftR_small : residualStage.leftR < prime
  leftZ_small : residualStage.leftZ < prime
  mixedY_small : residualStage.mixedCost.y < prime
  mixedR_small : residualStage.mixedCost.r < prime
  mixedZ_small : residualStage.mixedCost.z < prime

theorem residual_gates : ResidualGates := by constructor <;> decide

def ledger : ℕ := fixedRegularCap + fixedSingular.countCap +
  residualStage.regularCountCap + residualSingular.countCap + 1
theorem ledger_exact : ledger = 252125385273420115 := by
  rw [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, residualSingular_exact]
theorem ledger_lt : ledger < budget := by rw [ledger_exact]; decide

def radiusNumerator : ℕ := 10265855
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator

theorem radius_floor :
    ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    errors, IRSProfile.Index]
theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_root_integer : (2 : ℕ)^44 * 1000000^100 ≤ 1356605^100 := by decide
theorem score_radius_integer :
    (23288577 : ℕ)^128 * (2^67 * 1356605) ≤ 1000000 * 33554432^128 := by decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((44 : ℝ)/100) ≤ (1356605 : ℝ≥0)/1000000 := by
  have hroot : ((2 : ℝ≥0)^(44 : ℕ))^((100 : ℝ)⁻¹) ≤ (1356605 : ℝ≥0)/1000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((44 : ℝ)/100) = ((2 : ℝ≥0)^(44 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1356605) := by
  have hsub : (1 - radius : ℝ≥0) = 23288577/33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1356605)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6744 := by
  have hscale : (1000000 : ℝ≥0)/1356605 ≤ (2 : ℝ≥0)^(-((44 : ℝ)/100)) := by
    calc
      (1000000 : ℝ≥0)/1356605 = 1/((1356605 : ℝ≥0)/1000000) := by norm_num
      _ ≤ 1/((2 : ℝ≥0)^((44 : ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1356605) := radius_power_bound
    _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (2 : ℝ≥0)^(-((44 : ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6744 := by
      unfold claimedError
      rw [show -((((6744 : ℕ) : ℝ)/100)) =
          -((67 : ℕ) : ℝ) + -((44 : ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end
end ProximityPrize.SubmissionLower.LocatorArithmetic
