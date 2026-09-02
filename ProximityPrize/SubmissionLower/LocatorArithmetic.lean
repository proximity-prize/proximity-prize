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
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80565
def agreements:ℕ:=181579
def gap:ℕ:=50508
def prime:ℕ:=2130706433
def budget:ℕ:=274980725612371472
def LA:ℕ:=130000
def LB:ℕ:=6953
def LCap:ℕ:=3322
def yB:ℕ:=109
def sB:ℕ:=23
def yC:ℕ:=374
def sC:ℕ:=81
def weightedA:ℕ:=12347372
def weightedC:ℕ:=49026330
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=14344741
def weightedTCap:ℕ:=23968428
def fixedRegularCap:ℕ:=269054786353873127
theorem kernelA_rank:localRankBound 68 130000 20=4920190002:=by decide
theorem kernelC_rank:localRankBound 270 130000 81=296615133081:=by decide
theorem kernelB_rank:localRankBound 79 6953 23=403818520:=by decide
theorem kernelTCap_rank:localRankBound 132 3322 41=910154091:=by decide
theorem kernelA_nullity:
    coefficientCount 12347372 131071 130000 20 -
      262144 * localRankBound 68 130000 20=31493057617:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    12347372 131071 130000 20 95 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 49026330 131071 130000 81 -
      262144 * localRankBound 270 130000 81=500771585940295:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    49026330 131071 130000 81 375 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 14344741 131071 6953 23 -
      262144 * localRankBound 79 6953 23=11789310:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    14344741 131071 6953 23 110 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 23968428 131071 3322 41 -
      262144 * localRankBound 132 3322 41=109954663:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    23968428 131071 3322 41 183 (by decide) (by decide)]
  decide
theorem A_ys93_quotient_upper:
    coefficientCount 26718 131071 129906 20=3470855226:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    26718 131071 129906 20 1 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 23968428 131071 0 41 <
    coefficientCount 23968428 131071 3322 41 -
      262144 * localRankBound 132 3322 41:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,3321,20⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yC,sC,LA⟩
def chainStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem fixedSingular_exact:fixedSingular.countCap=970913371193501:=by decide
theorem residualStage_exact:residualStage.regularCountCap=3363962627119279:=by decide
theorem chainStage_exact:chainStage.regularCountCap=70633619230430:=by decide
theorem tailSingular_exact:tailSingular.countCap=1546818213171:=by decide
structure SingularGates (P:TightParameters):Prop where
  s_pos:1 ≤ P.s
  s_small:P.s < prime
  w_pos:1 ≤ P.w
  w_small:P.w < prime
  kD:P.w < P.kappa * P.D
  algebraic_pos:1 ≤ P.algebraicCap
  implicit_small:P.implicitYCap < prime
  algebraic_small:P.algebraicCap < prime
  mixed_small:2 * P.implicitYCap * P.algebraicCap < prime
  wa:P.w < P.a
  an:P.a ≤ P.n
theorem tail_singular_gates:SingularGates tailSingular:=by constructor <;> decide
structure ChainGates:Prop where
  qY:(tailSingular.D - 1) / w ≤ chainStage.leftY
  qR:tailSingular.s ≤ chainStage.leftR
  qZ:tailSingular.L ≤ chainStage.leftZ
  leftR_pos:1 ≤ chainStage.leftR
  leftY_small:chainStage.leftY < prime
  leftR_small:chainStage.leftR < prime
  leftZ_small:chainStage.leftZ < prime
  rightR_pos:1 ≤ chainStage.rightR
  rightY_small:chainStage.rightY < prime
  rightR_small:chainStage.rightR < prime
  rightZ_small:chainStage.rightZ < prime
  mixedY_small:chainStage.mixedCost.y < prime
  mixedR_small:chainStage.mixedCost.r < prime
  mixedZ_small:chainStage.mixedCost.z < prime
theorem chain_gates:ChainGates:=by constructor <;> decide
def ledger:ℕ:=fixedRegularCap + fixedSingular.countCap +
  residualStage.regularCountCap +
  (sB - 1) * chainStage.regularCountCap + (sB + 1) * tailSingular.countCap
theorem ledger_exact:ledger=274980725612371471:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10312376
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
theorem radius_floor:
    ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ =errors:=by
  norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    errors,IRSProfile.Index]
theorem radius_admissible:
    radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;> norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_root_integer:(2:ℕ)^81 * 389^100 ≤ 682^100:=by decide
theorem score_radius_integer:
    (23242056:ℕ)^128 * (2^67 * 682) ≤ 389 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((81:ℝ)/100) ≤ (682:ℝ≥0)/389:=by
  have hroot:((2:ℝ≥0)^(81:ℕ))^((100:ℝ)⁻¹) ≤ (682:ℝ≥0)/389:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((81:ℝ)/100) = ((2:ℝ≥0)^(81:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (389/682):=by
  have hsub:(1 - radius:ℝ≥0) =23242056/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (389/682)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6781:=by
  have hscale:(389:ℝ≥0)/682 ≤ (2:ℝ≥0)^(-((81:ℝ)/100)):=by
    calc
      (389:ℝ≥0)/682=1/((682:ℝ≥0)/389):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((81:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (389/682):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((81:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6781:=by
      unfold claimedError
      rw [show -((((6781:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((81:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
