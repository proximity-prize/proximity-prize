import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
import ProximityPrize.SubmissionLower.CommonShearTightPrototype
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
def errors:ℕ:=80535
def agreements:ℕ:=181609
def gap:ℕ:=50538
def prime:ℕ:=2130706433
def budget:ℕ:=274980725842294693
def LA:ℕ:=149307
def LB:ℕ:=5387
def LCap:ℕ:=3066
def weightedA:ℕ:=11986194
def weightedC:ℕ:=47944776
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=14347111
def weightedTCap:ℕ:=22882734
def fixedRegularCap:ℕ:=268081069281891082
theorem kernelA_rank:localRankBound 66 149307 19=5097886730:=by
  rw [← LocatorKernelEval.localRankBound_eq 66 149307 19 (by decide)]
  decide
theorem kernelC_rank:localRankBound 264 149307 80=321043224060:=by
  rw [← LocatorKernelEval.localRankBound_eq 264 149307 80 (by decide)]
  decide
theorem kernelB_rank:localRankBound 79 5387 23=312426760:=by
  rw [← LocatorKernelEval.localRankBound_eq 79 5387 23 (by decide)]
  decide
theorem kernelTCap_rank:localRankBound 126 3066 39=729508160:=by
  rw [← LocatorKernelEval.localRankBound_eq 126 3066 39 (by decide)]
  decide
theorem kernelA_nullity:
    coefficientCount 11986194 131071 149307 19 -
      262144 * localRankBound 66 149307 19=110752268665:=by
  rw [kernelA_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    11986194 131071 149307 19 92 (by decide) (by decide)]
  decide
theorem A_ys89_quotient_upper:
    coefficientCount 189823 131071 149217 19=45858751999:=by
  rw [LocatorKernelEval.coefficientCount_eq_cutoff
    189823 131071 149217 19 2 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 47944776 131071 149307 80 -
      262144 * localRankBound 264 149307 80=574559520456213:=by
  rw [kernelC_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    47944776 131071 149307 80 366 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 14347111 131071 5387 23 -
      262144 * localRankBound 79 5387 23=11512926:=by
  rw [kernelB_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    14347111 131071 5387 23 110 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 22882734 131071 3066 39 -
      262144 * localRankBound 126 3066 39=256570090:=by
  rw [kernelTCap_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    22882734 131071 3066 39 175 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 22882734 131071 2 39 <
    coefficientCount 22882734 131071 3066 39 -
      262144 * localRankBound 126 3066 39:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,3063,19⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,109,23,LB,365,80,LA⟩
def residualSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,23⟩
theorem fixedSingular_exact:fixedSingular.countCap=782020590180217:=by decide
theorem residualStage_exact:residualStage.regularCountCap=3682403618740941:=by decide
theorem residualSingular_exact:
    CommonShearTightPrototype.countCap residualSingular=2435232351482452:=by decide
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
  residualStage.regularCountCap +
    CommonShearTightPrototype.countCap residualSingular
theorem ledger_exact:ledger=274980725842294692:=by
  rw [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10308600
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
theorem score_root_integer:(2:ℕ)^78 * 251^100 ≤ 431^100:=by decide
theorem score_radius_integer:
    (23245832:ℕ)^128 * (2^67 * 431) ≤ 251 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((78:ℝ)/100) ≤ (431:ℝ≥0)/251:=by
  have hroot:((2:ℝ≥0)^(78:ℕ))^((100:ℝ)⁻¹) ≤ (431:ℝ≥0)/251:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((78:ℝ)/100) = ((2:ℝ≥0)^(78:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (251/431):=by
  have hsub:(1 - radius:ℝ≥0) =23245832/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (251/431)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6778:=by
  have hscale:(251:ℝ≥0)/431 ≤ (2:ℝ≥0)^(-((78:ℝ)/100)):=by
    calc
      (251:ℝ≥0)/431=1/((431:ℝ≥0)/251):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((78:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (251/431):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((78:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6778:=by
      unfold claimedError
      rw [show -((((6778:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((78:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
