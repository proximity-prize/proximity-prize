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
def errors:ℕ:=80496
def agreements:ℕ:=181648
def gap:ℕ:=50577
def prime:ℕ:=2130706433
def budget:ℕ:=274980726061438321
def LA:ℕ:=56863
def LB:ℕ:=4732
def LCap:ℕ:=2777
def weightedA:ℕ:=11443824
def weightedC:ℕ:=31970048
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=13805248
def weightedTCap:ℕ:=22342704
def fixedRegularCap:ℕ:=271584249856321201
theorem kernelA_rank:localRankBound 63 56863 18=1684637850:=by decide
theorem kernelC_rank:localRankBound 176 56863 52=35845255316:=by decide
theorem kernelB_rank:localRankBound 76 4732 22=243755886:=by decide
theorem kernelTCap_rank:localRankBound 123 2777 38=613496000:=by decide
theorem kernelA_nullity:
    coefficientCount 11443824 131071 56863 18 -
      262144 * localRankBound 63 56863 18=14369494135:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    11443824 131071 56863 18 88 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 31970048 131071 56863 52 -
      262144 * localRankBound 176 56863 52=55614698193593:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    31970048 131071 56863 52 244 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 13805248 131071 4732 22 -
      262144 * localRankBound 76 4732 22=21921507:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    13805248 131071 4732 22 106 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 22342704 131071 2777 38 -
      262144 * localRankBound 123 2777 38=267362810:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    22342704 131071 2777 38 171 (by decide) (by decide)]
  decide
theorem A_ys85_quotient_upper:
    coefficientCount 171736 131071 56777 18=14368556795:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    171736 131071 56777 18 2 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 22342704 131071 2 38 <
    coefficientCount 22342704 131071 2777 38 -
      262144 * localRankBound 123 2777 38:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,2774,18⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,105,22,LB,243,52,LA⟩
def residualSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,22⟩
theorem fixedSingular_exact:fixedSingular.countCap=604529466203000:=by decide
theorem residualStage_exact:residualStage.regularCountCap=913699404979338:=by decide
theorem residualSingular_exact:residualSingular.countCap=1878247333934781:=by decide
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
theorem ledger_exact:ledger=274980726061438320:=by
  rw [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10303615
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
theorem score_root_integer:(2:ℕ)^74 * 85^100 ≤ 142^100:=by decide
theorem score_radius_integer:
    (23250817:ℕ)^128 * (2^67 * 142) ≤ 85 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((74:ℝ)/100) ≤ (142:ℝ≥0)/85:=by
  have hroot:((2:ℝ≥0)^(74:ℕ))^((100:ℝ)⁻¹) ≤ (142:ℝ≥0)/85:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((74:ℝ)/100) = ((2:ℝ≥0)^(74:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (85/142):=by
  have hsub:(1 - radius:ℝ≥0) =23250817/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (85/142)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6774:=by
  have hscale:(85:ℝ≥0)/142 ≤ (2:ℝ≥0)^(-((74:ℝ)/100)):=by
    calc
      (85:ℝ≥0)/142=1/((142:ℝ≥0)/85):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((74:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (85/142):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((74:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6774:=by
      unfold claimedError
      rw [show -((((6774:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((74:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
