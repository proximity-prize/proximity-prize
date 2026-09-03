import ProximityPrize.SubmissionLower.LocatorPhase6802Certificate

namespace ProximityPrize.SubmissionLower.LocatorArithmetic6802

open ProximityPrize.Benchmark
open scoped BigOperators NNReal
open RCN100 RCN119 RCN302 RCN318 RCN260 LocatorFastKernelArithmetic

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def errors : ℕ := 80771
def agreements : ℕ := 181373
def gap : ℕ := 50302
def prime : ℕ := 2130706433
def budget : ℕ := 274980723145134423

def LA : ℕ := 130000
def LB : ℕ := 15200
def LCap : ℕ := 6408
def yB : ℕ := 149
def sB : ℕ := 32
def yT : ℕ := 258
def sT : ℕ := 58
def weightedA : ℕ := 17411808
def weightedB : ℕ := 19588284
def weightedTCap : ℕ := 33916751
def fixedRegularCap : ℕ := 257422060420373924

theorem kernelA_rank : localRankBound 96 130000 29 = 13837332645 := by
  rw [localRankBound_eq_fastLocalRankBound 96 130000 29 (by decide)]
  decide

theorem kernelB_rank : localRankBound 108 15200 32 = 2252617312 := by
  rw [localRankBound_eq_fastLocalRankBound 108 15200 32 (by decide)]
  decide

theorem kernelTCap_rank : localRankBound 187 6408 58 = 4958285424 := by
  rw [localRankBound_eq_fastLocalRankBound 187 6408 58 (by decide)]
  decide

theorem kernelA_nullity :
    coefficientCount 17411808 131071 130000 29 -
      262144 * localRankBound 96 130000 29 = 122788671575 := by
  rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    17411808 131071 130000 29 133 (by decide) (by decide)]
  decide

theorem kernelB_nullity :
    coefficientCount 19588284 131071 15200 32 -
      262144 * localRankBound 108 15200 32 = 1001019316 := by
  rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    19588284 131071 15200 32 150 (by decide) (by decide)]
  decide

theorem kernelTCap_nullity :
    coefficientCount 33916751 131071 6408 58 -
      262144 * localRankBound 187 6408 58 = 1282853579 := by
  rw [kernelTCap_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    33916751 131071 6408 58 259 (by decide) (by decide)]
  decide

theorem kernelTCap_total_quotient_lt :
    coefficientCount 33916751 131071 4 58 <
      coefficientCount 33916751 131071 6408 58 -
        262144 * localRankBound 187 6408 58 := by
  rw [kernelTCap_nullity]
  decide

def fixedSingular : TightParameters :=
  ⟨n, w, agreements, weightedB, 6403, sB⟩

def residualStage : UnequalParameters :=
  ⟨n, w, agreements, yB, sB, LB, yT, sT, LCap⟩

def chainStage : UnequalParameters :=
  ⟨n, w, agreements, yB, sB - 1, LB, yB, sB, LB⟩

def tailSingular : TightParameters :=
  ⟨n, w, agreements, weightedB, LB, 1⟩

def fixedSingularCap : ℕ :=
  CommonShearTightPrototype.countCap fixedSingular

theorem fixedSingular_exact : fixedSingularCap = 7783031485265339 := by decide

theorem residualStage_exact :
    residualStage.regularCountCap = 558478188958411 := by decide

theorem chainStage_exact :
    chainStage.regularCountCap = 292386546585849 := by decide

theorem tailSingular_exact : tailSingular.countCap = 4641518375013 := by decide

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

theorem tail_singular_gates : SingularGates tailSingular := by
  constructor <;> decide

structure ChainGates : Prop where
  qY : (tailSingular.D - 1) / w ≤ chainStage.leftY
  qR : tailSingular.s ≤ chainStage.leftR
  qZ : tailSingular.L ≤ chainStage.leftZ
  leftR_pos : 1 ≤ chainStage.leftR
  leftY_small : chainStage.leftY < prime
  leftR_small : chainStage.leftR < prime
  leftZ_small : chainStage.leftZ < prime
  rightR_pos : 1 ≤ chainStage.rightR
  rightY_small : chainStage.rightY < prime
  rightR_small : chainStage.rightR < prime
  rightZ_small : chainStage.rightZ < prime
  mixedY_small : chainStage.mixedCost.y < prime
  mixedR_small : chainStage.mixedCost.r < prime
  mixedZ_small : chainStage.mixedCost.z < prime

theorem chain_gates : ChainGates := by
  constructor <;> decide

def ledger : ℕ := fixedRegularCap + fixedSingularCap +
  residualStage.regularCountCap +
  (sB - 1) * chainStage.regularCountCap +
  (sB + 1) * tailSingular.countCap

theorem ledger_exact : ledger = 274980723145134422 := by
  norm_num [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, chainStage_exact, tailSingular_exact, sB]

theorem ledger_lt : ledger < budget := by
  rw [ledger_exact]
  decide

def radiusNumerator : ℕ := 10338815
def radiusDenominator : ℕ := 33554432
def radius : ℝ≥0 := claimedRadius radiusNumerator radiusDenominator

theorem radius_floor :
    ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors := by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    errors, IRSProfile.Index]

theorem radius_admissible :
    radius ∈ Set.Ioo (0 : ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;>
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
      IRSProfile.minRelativeDistance]

theorem score_root_integer : (2 : ℕ) * 143 ^ 50 ≤ 145 ^ 50 := by decide

theorem two_rpow_fraction_le :
    (2 : ℝ≥0) ^ ((1 : ℝ) / 50) ≤ (145 : ℝ≥0) / 143 := by
  rw [one_div, NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 50),
    NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
  exact_mod_cast score_root_integer

theorem score_radius_integer :
    (23215617 : ℕ) ^ 128 * (2 ^ 68 * 145) ≤
      143 * 33554432 ^ 128 := by decide

theorem radius_power_bound :
    (1 - radius) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) * (143 / 145) := by
  have hsub : (1 - radius : ℝ≥0) = 23215617 / 33554432 := by
    have hr : radius ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius) ^ 128 ≤
    ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) * (143 / 145)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer

theorem score_target_le :
    (1 - radius) ^ IRSProfile.repetitions ≤ claimedError 6802 := by
  have hscale : (143 : ℝ≥0) / 145 ≤
      (2 : ℝ≥0) ^ (-((1 : ℝ) / 50)) := by
    calc
      (143 : ℝ≥0) / 145 = 1 / ((145 : ℝ≥0) / 143) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((1 : ℝ) / 50)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _ := by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) * (143 / 145) := radius_power_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (68 : ℕ)) *
        (2 : ℝ≥0) ^ (-((1 : ℝ) / 50)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6802 := by
      unfold claimedError
      rw [show -((((6802 : ℕ) : ℝ) / 100)) =
          -((68 : ℕ) : ℝ) + -((1 : ℝ) / 50) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

end

end ProximityPrize.SubmissionLower.LocatorArithmetic6802
