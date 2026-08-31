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
def errors : ℕ := 80270
def agreements : ℕ := 181874
def gap : ℕ := 50803
def prime : ℕ := 2130706433
def budget : ℕ := 274980726811395087
def LA : ℕ := 109000
def Laux : ℕ := 10000
def LB : ℕ := 1702
def weightedA : ℕ := 8729952
def weightedAux : ℕ := 11094314
def weightedC : ℕ := 12367432
abbrev weightedAmbient := weightedC
def weightedB : ℕ := 17096156
def fixedRegularCap : ℕ := 266000000000000000

theorem row_values : agreements + errors = n ∧ agreements - w = gap ∧
    weightedA = 48 * agreements ∧ weightedAux = 61 * agreements ∧
    weightedC = 68 * agreements ∧ weightedB = 94 * agreements ∧ w < agreements ∧
    w + 1 ≤ weightedA ∧ weightedC < prime := by decide

theorem kernelA_rank : localRankBound 48 109000 14 = 1483764030 := by decide
theorem kernelAux_rank : localRankBound 61 10000 18 = 275359875 := by decide
theorem kernelC_rank : localRankBound 68 10000 20 = 377470002 := by decide
theorem kernelB_rank : localRankBound 94 1702 29 = 168798135 := by decide

theorem kernelA_nullity :
    coefficientCount 8729952 131071 109000 14 -
      262144 * localRankBound 48 109000 14 = 40187679250 := by
  rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    8729952 131071 109000 14 67 (by decide) (by decide)]
  decide
theorem kernelAux_nullity :
    coefficientCount 11094314 131071 10000 18 -
      262144 * localRankBound 61 10000 18 = 147868193652 := by
  rw [kernelAux_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    11094314 131071 10000 18 85 (by decide) (by decide)]
  decide
theorem kernelC_nullity :
    coefficientCount 12367432 131071 10000 20 -
      262144 * localRankBound 68 10000 20 = 291151498617 := by
  rw [kernelC_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    12367432 131071 10000 20 95 (by decide) (by decide)]
  decide
theorem kernelB_nullity :
    coefficientCount 17096156 131071 1702 29 -
      262144 * localRankBound 94 1702 29 = 401799790 := by
  rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    17096156 131071 1702 29 131 (by decide) (by decide)]
  decide

theorem A_ys65_quotient_upper :
    coefficientCount 210351 131071 108935 14 = 40187639071 := by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    210351 131071 108935 14 2 (by decide) (by decide)]
  decide

theorem kernelA_ys65_quotient_lt (r : ℕ) (hr : r ≤ 14) :
    coefficientCount (8729952 - (65 * 131071 - r)) 131071
      (109000 - 65) (14 - r) <
    coefficientCount 8729952 131071 109000 14 -
      262144 * localRankBound 48 109000 14 := by
  rw [kernelA_nullity]
  have hmono := RCN180.Numeric6733.coefficientCount_mono_D_s
    (D := 8729952 - (65 * 131071 - r)) (D' := 210351)
    (w := 131071) (L := 108935) (s := 14 - r) (s' := 14)
    (by omega) (by omega)
  rw [A_ys65_quotient_upper] at hmono
  exact hmono.trans_lt (by decide)

theorem kernelB_total_quotient_lt :
    coefficientCount 17096156 131071 3 29 <
    coefficientCount 17096156 131071 1702 29 -
      262144 * localRankBound 94 1702 29 := by
  rw [kernelB_nullity]
  decide

def fixedSingular : TightParameters := ⟨n, w, agreements, weightedA, 1698, 14⟩
def residualStage : UnequalParameters := ⟨n, w, agreements, 130, 29, LB, 94, 20, LA⟩
def residualSingular : TightParameters := ⟨n, w, agreements, weightedB, LB, 29⟩

theorem fixedSingular_exact : fixedSingular.countCap = 167256949628031 := by decide
theorem residualStage_exact : residualStage.regularCountCap = 949770519237267 := by decide
theorem residualSingular_exact : residualSingular.countCap = 1463337411915888 := by decide

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
theorem ledger_exact : ledger = 268580364880781187 := by
  rw [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, residualSingular_exact]
theorem ledger_lt : ledger < budget := by rw [ledger_exact]; decide

def radiusNumerator : ℕ := 10274587
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
theorem score_root_integer : (2 : ℕ)^51 * 1000000^100 ≤ 1424051^100 := by decide
theorem score_radius_integer :
    (23279845 : ℕ)^128 * (2^67 * 1424051) ≤ 1000000 * 33554432^128 := by decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0)^((51 : ℝ)/100) ≤ (1424051 : ℝ≥0)/1000000 := by
  have hroot : ((2 : ℝ≥0)^(51 : ℕ))^((100 : ℝ)⁻¹) ≤ (1424051 : ℝ≥0)/1000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2 : ℝ≥0)^((51 : ℝ)/100) = ((2 : ℝ≥0)^(51 : ℕ))^((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _ := hroot

theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1424051) := by
  have hsub : (1 - radius : ℝ≥0) = 23279845/33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1424051)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6751 := by
  have hscale : (1000000 : ℝ≥0)/1424051 ≤ (2 : ℝ≥0)^(-((51 : ℝ)/100)) := by
    calc
      (1000000 : ℝ≥0)/1424051 = 1/((1424051 : ℝ≥0)/1000000) := by norm_num
      _ ≤ 1/((2 : ℝ≥0)^((51 : ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1 : ℝ≥0)/2^(67 : ℕ)) * (1000000/1424051) := radius_power_bound
    _ ≤ ((1 : ℝ≥0)/2^(67 : ℕ)) * (2 : ℝ≥0)^(-((51 : ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6751 := by
      unfold claimedError
      rw [show -((((6751 : ℕ) : ℝ)/100)) =
          -((67 : ℕ) : ℝ) + -((51 : ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end
end ProximityPrize.SubmissionLower.LocatorArithmetic
