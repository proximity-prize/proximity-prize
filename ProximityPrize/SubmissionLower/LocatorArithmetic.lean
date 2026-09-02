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
def errors:ℕ:=80660
def agreements:ℕ:=181484
def gap:ℕ:=50413
def prime:ℕ:=2130706433
def budget:ℕ:=274980724793190814
def LA:ℕ:=127295
def LB:ℕ:=10000
def LCap:ℕ:=6000
def weightedA:ℕ:=14518720
def weightedC:ℕ:=33756024
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=17059496
def weightedTCap:ℕ:=23229952
def fixedRegularCap:ℕ:=135101317857843592
theorem kernelA_rank:localRankBound 80 127295 24=7877437800:=by decide
theorem kernelC_rank:localRankBound 186 127295 55=94702619396:=by decide
theorem kernelB_rank:localRankBound 94 10000 28=986345680:=by decide
theorem kernelTCap_rank:localRankBound 128 6000 39=1491618280:=by decide
theorem kernelA_nullity:
    coefficientCount 14518720 131071 127295 24 -
      262144 * localRankBound 80 127295 24=356506352075:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    14518720 131071 127295 24 111 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 33756024 131071 127295 55 -
      262144 * localRankBound 186 127295 55=106034443540158:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    33756024 131071 127295 55 258 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 17059496 131071 10000 28 -
      262144 * localRankBound 94 10000 28=78592203043:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    17059496 131071 10000 28 131 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 23229952 131071 6000 39 -
      262144 * localRankBound 128 6000 39=282216482070:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    23229952 131071 6000 39 178 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 23229952 131071 2 39 <
    coefficientCount 23229952 131071 6000 39 -
      262144 * localRankBound 128 6000 39:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,4000,24⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,130,28,LB,257,55,LA⟩
def residualSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,28⟩
theorem fixedSingular_exact:fixedSingular.countCap=2001271474091785:=by decide
theorem residualStage_exact:residualStage.regularCountCap=2675477211695642:=by decide
theorem residualSingular_exact:residualSingular.countCap=8050365797797609:=by decide
structure SingularGates (P:TightParameters):Prop where
  s_pos:1 ≤ P.s
  s_small:P.s < prime
  w_pos:1 ≤ P.w
  w_small:P.w < prime
  kD:P.w < P.kappa * P.D
  algebraic_pos:1 ≤ P.algebraicCap
  implicit_small:P.implicitYCap < prime
  algebraic_small:P.algebraicCap < prime
  wa:P.w < P.a
  an:P.a ≤ P.n
theorem residual_singular_gates:SingularGates residualSingular:=by constructor <;> decide
structure ResidualGates:Prop where
  qY:(residualSingular.D - 1) / w ≤ residualStage.leftY
  qR:residualSingular.s ≤ residualStage.leftR
  qZ:residualSingular.L ≤ residualStage.leftZ
  rightY:(weightedAmbient - 1) / w ≤ residualStage.rightY
  leftR_pos:1 ≤ residualStage.leftR
  leftY_small:residualStage.leftY < prime
  leftR_small:residualStage.leftR < prime
  leftZ_small:residualStage.leftZ < prime
  mixedY_small:residualStage.mixedCost.y < prime
  mixedR_small:residualStage.mixedCost.r < prime
  mixedZ_small:residualStage.mixedCost.z < prime
theorem residual_gates:ResidualGates:=by constructor <;> decide
def ledger:ℕ:=fixedRegularCap + fixedSingular.countCap +
  residualStage.regularCountCap + residualSingular.countCap
theorem ledger_exact:ledger=147828432341428628:=by
  rw [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10324607
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
theorem score_root_integer:(2:ℕ)^9 * 15^10 ≤ 28^10:=by decide
theorem score_radius_integer:
    (23229825:ℕ)^128 * (2^67 * 28) ≤ 15 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((90:ℝ)/100) ≤ (28:ℝ≥0)/15:=by
  have hroot:((2:ℝ≥0)^(9:ℕ))^((10:ℝ)⁻¹) ≤ (28:ℝ≥0)/15:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 10)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((90:ℝ)/100) = ((2:ℝ≥0)^(9:ℕ))^((10:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (15/28):=by
  have hsub:(1 - radius:ℝ≥0) =23229825/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (15/28)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6790:=by
  have hscale:(15:ℝ≥0)/28 ≤ (2:ℝ≥0)^(-((90:ℝ)/100)):=by
    calc
      (15:ℝ≥0)/28=1/((28:ℝ≥0)/15):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((90:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (15/28):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((90:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6790:=by
      unfold claimedError
      rw [show -((((6790:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((90:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
