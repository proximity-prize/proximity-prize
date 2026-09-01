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
def errors:ℕ:=80526
def agreements:ℕ:=181618
def gap:ℕ:=50547
def prime:ℕ:=2130706433
def budget:ℕ:=274980725868189680
def LA:ℕ:=230000
def LB:ℕ:=5047
def LCap:ℕ:=2994
def weightedA:ℕ:=11623552
def weightedC:ℕ:=43769938
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=14347822
def weightedTCap:ℕ:=22883868
def fixedRegularCap:ℕ:=266990962477160602
theorem kernelA_rank:localRankBound 64 230000 19=7338435320:=by decide
theorem kernelC_rank:localRankBound 241 230000 71=369080264856:=by decide
theorem kernelB_rank:localRankBound 79 5047 23=292584360:=by decide
theorem kernelTCap_rank:localRankBound 126 2994 39=712062560:=by decide
theorem kernelA_nullity:
    coefficientCount 11623552 131071 230000 19 -
      262144 * localRankBound 64 230000 19=31252469225:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    11623552 131071 230000 19 89 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 43769938 131071 230000 71 -
      262144 * localRankBound 241 230000 71=646245243669294:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    43769938 131071 230000 71 334 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 14347822 131071 5047 23 -
      262144 * localRankBound 79 5047 23=9311742:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    14347822 131071 5047 23 110 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 22883868 131071 2994 39 -
      262144 * localRankBound 126 2994 39=112304770:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    22883868 131071 2994 39 175 (by decide) (by decide)]
  decide
theorem A_ys87_quotient_upper:
    coefficientCount 89323 131071 229912 19=20536518899:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    89323 131071 229912 19 1 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 22883868 131071 1 39 <
    coefficientCount 22883868 131071 2994 39 -
      262144 * localRankBound 126 2994 39:=by
  rw [kernelTCap_nullity]
  decide
theorem kernelTCap_total_quotient_next:
    coefficientCount 22883868 131071 2 39=227527975:=by decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,2992,19⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,109,23,LB,333,71,LA⟩
def residualSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,23⟩
theorem fixedSingular_exact:fixedSingular.countCap=740729750149629:=by decide
theorem residualStage_exact:residualStage.regularCountCap=4967917024286099:=by decide
theorem residualSingular_exact:residualSingular.countCap=2281116616593349:=by decide
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
theorem ledger_exact:ledger=274980725868189679:=by
  rw [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10307341
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
theorem score_root_integer:(2:ℕ)^77 * 1252^100 ≤ 2135^100:=by decide
theorem score_radius_integer:
    (23247091:ℕ)^128 * (2^67 * 2135) ≤ 1252 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((77:ℝ)/100) ≤ (2135:ℝ≥0)/1252:=by
  have hroot:((2:ℝ≥0)^(77:ℕ))^((100:ℝ)⁻¹) ≤ (2135:ℝ≥0)/1252:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((77:ℝ)/100) = ((2:ℝ≥0)^(77:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (1252/2135):=by
  have hsub:(1 - radius:ℝ≥0) =23247091/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (1252/2135)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6777:=by
  have hscale:(1252:ℝ≥0)/2135 ≤ (2:ℝ≥0)^(-((77:ℝ)/100)):=by
    calc
      (1252:ℝ≥0)/2135=1/((2135:ℝ≥0)/1252):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((77:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (1252/2135):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((77:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6777:=by
      unfold claimedError
      rw [show -((((6777:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((77:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
