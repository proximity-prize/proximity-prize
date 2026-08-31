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
def errors : ℕ := 80299
def agreements : ℕ := 181845
def gap : ℕ := 50774
def prime : ℕ := 2130706433
def budget : ℕ := 274980726811395087
def LA : ℕ := 100000
def Laux : ℕ := 100000
def LB : ℕ := 1799
def weightedA : ℕ := 9092250
def weightedAux : ℕ := 9092250
def weightedC : ℕ := 13456530
abbrev weightedAmbient := weightedC
def weightedB : ℕ := 17638965
def fixedRegularCap : ℕ := 269000000000000000

theorem row_values : agreements + errors = n ∧ agreements - w = gap ∧
    weightedA = 50 * agreements ∧ weightedAux = 50 * agreements ∧
    weightedC = 74 * agreements ∧ weightedB = 97 * agreements ∧ w < agreements ∧
    w + 1 ≤ weightedA ∧ weightedC < prime := by decide

theorem kernelA_rank : localRankBound 50 100000 14 = 1488694080 := by decide
theorem kernelAux_rank : localRankBound 50 100000 15 = 1563672240 := by decide
theorem kernelC_rank : localRankBound 74 2773 22 = 134051774 := by decide
theorem kernelB_rank : localRankBound 97 1799 30 = 196219894 := by decide

theorem kernelA_nullity :
    coefficientCount 9092250 131071 100000 14 -
      262144 * localRankBound 50 100000 14 = 23319716365 := by
  rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9092250 131071 100000 14 70 (by decide) (by decide)]
  decide
theorem kernelAux_nullity :
    coefficientCount 9092250 131071 100000 15 -
      262144 * localRankBound 50 100000 15 = 92028762220 := by
  rw [kernelAux_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9092250 131071 100000 15 70 (by decide) (by decide)]
  decide
theorem kernelC_nullity :
    coefficientCount 13456530 131071 2773 22 -
      262144 * localRankBound 74 2773 22 = 38932026630 := by
  rw [kernelC_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13456530 131071 2773 22 103 (by decide) (by decide)]
  decide
theorem kernelB_nullity :
    coefficientCount 17638965 131071 1799 30 -
      262144 * localRankBound 97 1799 30 = 223918084 := by
  rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    17638965 131071 1799 30 135 (by decide) (by decide)]
  decide

theorem Aux_ys67_r13_quotient_exact :
    coefficientCount 310506 131071 99933 2 = 81392795787 := by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    310506 131071 99933 2 3 (by decide) (by decide)]
  decide

theorem kernelAux_ys67_quotient_lt (r : ℕ) (hr : r ≤ 15) :
    coefficientCount (9092250 - (67 * 131071 - r)) 131071
      (100000 - 67) (15 - r) <
    coefficientCount 9092250 131071 100000 15 -
      262144 * localRankBound 50 100000 15 := by
  rw [kernelAux_nullity]
  interval_cases r <;>
    rw [coefficientCount_eq_sum_range_of_weighted_cutoff
      _ 131071 99933 _ 3 (by decide) (by decide)] <;> decide

theorem kernelB_total_quotient_lt :
    coefficientCount 17638965 131071 2 30 <
    coefficientCount 17638965 131071 1799 30 -
      262144 * localRankBound 97 1799 30 := by
  rw [kernelB_nullity]
  decide

def fixedSingular : TightParameters := ⟨n, w, agreements, weightedA, 1796, 14⟩
def residualStage : UnequalParameters := ⟨n, w, agreements, 134, 30, LB, 102, 22, LA⟩
def residualSingular : TightParameters := ⟨n, w, agreements, weightedB, LB, 30⟩

theorem fixedSingular_exact : fixedSingular.countCap = 184296506270351 := by decide
theorem residualStage_exact : residualStage.regularCountCap = 953373698228836 := by decide
theorem residualSingular_exact : residualSingular.countCap = 1710742257511041 := by decide

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
  residualStage.regularCountCap + residualSingular.countCap + 1
theorem ledger_exact : ledger = 271848412462010229 := by
  rw [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, residualSingular_exact]
theorem ledger_lt : ledger < budget := by rw [ledger_exact]; decide

def radiusNumerator : ℕ := 10278369
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
theorem score_root_integer : (2 : ℕ)^54 * 1000000^100 ≤ 1453973^100 := by decide
theorem score_radius_integer :
    (23276063 : ℕ)^128 * (2^67 * 1453973) ≤ 1000000 * 33554432^128 := by decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((54 : ℝ)/100) ≤ (1453973 : ℝ≥0)/1000000 := by
  have hroot : ((2 : ℝ≥0)^(54 : ℕ))^((100 : ℝ)⁻¹) ≤ (1453973 : ℝ≥0)/1000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((54 : ℝ)/100) = ((2 : ℝ≥0)^(54 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1453973) := by
  have hsub : (1 - radius : ℝ≥0) = 23276063/33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1453973)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6754 := by
  have hscale : (1000000 : ℝ≥0)/1453973 ≤ (2 : ℝ≥0)^(-((54 : ℝ)/100)) := by
    calc
      (1000000 : ℝ≥0)/1453973 = 1/((1453973 : ℝ≥0)/1000000) := by norm_num
      _ ≤ 1/((2 : ℝ≥0)^((54 : ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1453973) := radius_power_bound
    _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (2 : ℝ≥0)^(-((54 : ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6754 := by
      unfold claimedError
      rw [show -((((6754 : ℕ) : ℝ)/100)) =
          -((67 : ℕ) : ℝ) + -((54 : ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end
end ProximityPrize.SubmissionLower.LocatorArithmetic
