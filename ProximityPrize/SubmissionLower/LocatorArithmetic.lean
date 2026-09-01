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
def errors:ℕ:=80516
def agreements:ℕ:=181628
def gap:ℕ:=50557
def prime:ℕ:=2130706433
def budget:ℕ:=274980725894119306
def LA:ℕ:=169536
def LB:ℕ:=4893
def LCap:ℕ:=2919
def weightedA:ℕ:=11624192
def weightedC:ℕ:=39050020
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=13985356
def weightedTCap:ℕ:=22885128
def fixedRegularCap:ℕ:=268872673633727229
theorem kernelA_rank:localRankBound 64 169536 19=5409029080:=by decide
theorem kernelC_rank:localRankBound 215 169536 63=192822640512:=by decide
theorem kernelB_rank:localRankBound 77 4893 23=268004384:=by decide
theorem kernelTCap_rank:localRankBound 126 2919 39=693890060:=by decide
theorem kernelA_nullity:
    coefficientCount 11624192 131071 169536 19 -
      262144 * localRankBound 64 169536 19=180306218025:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    11624192 131071 169536 19 89 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 39050020 131071 169536 63 -
      262144 * localRankBound 215 169536 63=325815967324336:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    39050020 131071 169536 63 298 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 13985356 131071 4893 23 -
      262144 * localRankBound 77 4893 23=17777742:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    13985356 131071 4893 23 107 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 22885128 131071 2919 39 -
      262144 * localRankBound 126 2919 39=265072570:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    22885128 131071 2919 39 175 (by decide) (by decide)]
  decide
theorem A_ys85_quotient_upper:
    coefficientCount 352105 131071 169450 19=180306065913:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    352105 131071 169450 19 3 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 22885128 131071 2 39 <
    coefficientCount 22885128 131071 2919 39 -
      262144 * localRankBound 126 2919 39:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,2916,19⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,106,23,LB,297,63,LA⟩
def residualSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,23⟩
theorem fixedSingular_exact:fixedSingular.countCap=721771034761840:=by decide
theorem residualStage_exact:residualStage.regularCountCap=3230876361652506:=by decide
theorem residualSingular_exact:residualSingular.countCap=2155404863977730:=by decide
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
theorem ledger_exact:ledger=274980725894119305:=by
  rw [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10306082
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
theorem score_root_integer:(2:ℕ)^19 * 845^25 ≤ 1431^25:=by decide
theorem score_radius_integer:
    (23248350:ℕ)^128 * (2^67 * 1431) ≤ 845 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((76:ℝ)/100) ≤ (1431:ℝ≥0)/845:=by
  have hroot:((2:ℝ≥0)^(19:ℕ))^((25:ℝ)⁻¹) ≤ (1431:ℝ≥0)/845:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 25)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((76:ℝ)/100) = ((2:ℝ≥0)^(19:ℕ))^((25:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (845/1431):=by
  have hsub:(1 - radius:ℝ≥0) =23248350/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (845/1431)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6776:=by
  have hscale:(845:ℝ≥0)/1431 ≤ (2:ℝ≥0)^(-((76:ℝ)/100)):=by
    calc
      (845:ℝ≥0)/1431=1/((1431:ℝ≥0)/845):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((76:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (845/1431):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((76:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6776:=by
      unfold claimedError
      rw [show -((((6776:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((76:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
