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
def errors:ℕ:=80408
def agreements:ℕ:=181736
def gap:ℕ:=50665
def prime:ℕ:=2130706433
def budget:ℕ:=274980726466479100
def LA:ℕ:=55600
def LB:ℕ:=2321
def weightedA:ℕ:=10358952
def weightedC:ℕ:=23443944
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=17264920
def fixedRegularCap:ℕ:=271797226259522258
theorem kernelA_rank:localRankBound 57 55600 17=1268132553:=by decide
theorem kernelThin_rank:localRankBound 57 55600 16=1214066101:=by decide
theorem kernelC_rank:localRankBound 129 55600 40=14449335005:=by decide
theorem kernelB_rank:localRankBound 95 2321 29=237171065:=by decide
theorem kernelA_nullity:
    coefficientCount 10358952 131071 55600 17 -
      262144 * localRankBound 57 55600 17=75214362891:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    10358952 131071 55600 17 80 (by decide) (by decide)]
  decide
theorem kernelThin_nullity:
    coefficientCount 10358952 131071 55600 16 -
      262144 * localRankBound 57 55600 16=9871262228:=by
  rw [kernelThin_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    10358952 131071 55600 16 80 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 23443944 131071 55600 40 -
      262144 * localRankBound 129 55600 40=22443971469480:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    23443944 131071 55600 40 179 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 17264920 131071 2321 29 -
      262144 * localRankBound 95 2321 29=156094065:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    17264920 131071 2321 29 132 (by decide) (by decide)]
  decide
theorem A_ys76_quotient_upper:
    coefficientCount 397573 131071 55524 17=75197220065:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    397573 131071 55524 17 4 (by decide) (by decide)]
  decide
theorem kernelB_total_quotient_lt:
    coefficientCount 17264920 131071 1 29 <
    coefficientCount 17264920 131071 2321 29 -
      262144 * localRankBound 95 2321 29:=by
  rw [kernelB_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,2319,16⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,131,29,LB,178,40,LA⟩
def residualSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,29⟩
theorem fixedSingular_exact:fixedSingular.countCap=358347474941355:=by decide
theorem residualStage_exact:residualStage.regularCountCap=804252058981219:=by decide
theorem residualSingular_exact:residualSingular.countCap=2020900673034267:=by decide
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
theorem ledger_exact:ledger=274980726466479099:=by
  rw [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10292230
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
theorem score_root_integer:(2:ℕ)^13 * 1000000000^20 ≤ 1569168196^20:=by decide
theorem score_radius_integer:
    (23262202:ℕ)^128 * (2^67 * 1569168196) ≤ 1000000000 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((13:ℝ)/20) ≤ (1569168196:ℝ≥0)/1000000000:=by
  have hroot:((2:ℝ≥0)^(13:ℕ))^((20:ℝ)⁻¹) ≤ (1569168196:ℝ≥0)/1000000000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 20)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((13:ℝ)/20) = ((2:ℝ≥0)^(13:ℕ))^((20:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1569168196):=by
  have hsub:(1 - radius:ℝ≥0) =23262202/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1569168196)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6765:=by
  have hscale:(1000000000:ℝ≥0)/1569168196 ≤ (2:ℝ≥0)^(-((13:ℝ)/20)):=by
    calc
      (1000000000:ℝ≥0)/1569168196=1/((1569168196:ℝ≥0)/1000000000):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((13:ℝ)/20)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1569168196):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((13:ℝ)/20)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6765:=by
      unfold claimedError
      rw [show -((((6765:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((13:ℝ)/20) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
