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
def errors:ℕ:=80427
def agreements:ℕ:=181717
def gap:ℕ:=50646
def prime:ℕ:=2130706433
def budget:ℕ:=274980726401750329
def LA:ℕ:=52091
def LB:ℕ:=2452
def weightedA:ℕ:=10539586
def weightedC:ℕ:=22896342
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=17081398
def fixedRegularCap:ℕ:=271696008548359000
theorem kernelA_rank:localRankBound 58 52091 17=1234448256:=by decide
theorem kernelThin_rank:localRankBound 58 52091 17=1234448256:=by decide
theorem kernelC_rank:localRankBound 126 52091 39=12608265660:=by decide
theorem kernelB_rank:localRankBound 94 2452 29=245009385:=by decide
theorem kernelA_nullity:
    coefficientCount 10539586 131071 52091 17 -
      262144 * localRankBound 58 52091 17=59324346036:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    10539586 131071 52091 17 81 (by decide) (by decide)]
  decide
theorem kernelThin_nullity:
    coefficientCount 10539586 131071 52091 17 -
      262144 * localRankBound 58 52091 17=59324346036:=by
  rw [kernelThin_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    10539586 131071 52091 17 81 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 22896342 131071 52091 39 -
      262144 * localRankBound 126 52091 39=18421074905050:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    22896342 131071 52091 39 175 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 17081398 131071 2452 29 -
      262144 * localRankBound 94 2452 29=147311280:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    17081398 131071 2452 29 131 (by decide) (by decide)]
  decide
theorem A_ys78_quotient_upper:
    coefficientCount 316065 131071 52013 17=44098128031:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    316065 131071 52013 17 3 (by decide) (by decide)]
  decide
theorem kernelB_total_quotient_lt:
    coefficientCount 17081398 131071 1 29 <
    coefficientCount 17081398 131071 2452 29 -
      262144 * localRankBound 94 2452 29:=by
  rw [kernelB_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,2450,17⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,130,29,LB,174,39,LA⟩
def residualSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,29⟩
theorem fixedSingular_exact:fixedSingular.countCap=436572569041217:=by decide
theorem residualStage_exact:residualStage.regularCountCap=735136407288493:=by decide
theorem residualSingular_exact:residualSingular.countCap=2113008877061618:=by decide
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
theorem ledger_exact:ledger=274980726401750328:=by
  rw [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10294749
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
theorem score_root_integer:(2:ℕ)^67 * 1000000000^100 ≤ 1591072968^100:=by decide
theorem score_radius_integer:
    (23259683:ℕ)^128 * (2^67 * 1591072968) ≤ 1000000000 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((67:ℝ)/100) ≤ (1591072968:ℝ≥0)/1000000000:=by
  have hroot:((2:ℝ≥0)^(67:ℕ))^((100:ℝ)⁻¹) ≤ (1591072968:ℝ≥0)/1000000000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((67:ℝ)/100) = ((2:ℝ≥0)^(67:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1591072968):=by
  have hsub:(1 - radius:ℝ≥0) =23259683/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1591072968)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6767:=by
  have hscale:(1000000000:ℝ≥0)/1591072968 ≤ (2:ℝ≥0)^(-((67:ℝ)/100)):=by
    calc
      (1000000000:ℝ≥0)/1591072968=1/((1591072968:ℝ≥0)/1000000000):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((67:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1591072968):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((67:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6767:=by
      unfold claimedError
      rw [show -((((6767:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((67:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
