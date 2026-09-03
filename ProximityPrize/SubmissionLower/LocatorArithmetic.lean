import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
import ProximityPrize.SubmissionLower.CommonShearTightPrototype
import ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic
import ProximityPrize.SubmissionLower.LocatorChainArithmetic
namespace ProximityPrize.SubmissionLower.LocatorArithmetic
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
open RCN100 RCN119 RCN302 RCN318 RCN260 LocatorFastKernelArithmetic
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80752
def agreements:ℕ:=181392
def gap:ℕ:=50321
def prime:ℕ:=2130706433
def budget:ℕ:=274980723472028131
def LA:ℕ:=130000
def LB:ℕ:=10381
def LCap:ℕ:=5968
def yB:ℕ:=153
def sB:ℕ:=33
def yC:ℕ:=373
def sC:ℕ:=81
def yT:ℕ:=250
def sT:ℕ:=56
def weightedA:ℕ:=16688064
def weightedC:ℕ:=48975840
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=20134512
def weightedTCap:ℕ:=32831952
def fixedRegularCap:ℕ:=259787835303351020
theorem kernelA_rank:localRankBound 92 130000 28=12271362702:=by
  rw [localRankBound_eq_fastLocalRankBound 92 130000 28 (by decide)]
  decide
theorem kernelC_rank:localRankBound 270 130000 81=296615133081:=by
  rw [localRankBound_eq_fastLocalRankBound 270 130000 81 (by decide)]
  decide
theorem kernelB_rank:localRankBound 111 10381 33=1669841677:=by
  rw [localRankBound_eq_fastLocalRankBound 111 10381 33 (by decide)]
  decide
theorem kernelTCap_rank:localRankBound 181 5968 56=4181070327:=by
  rw [localRankBound_eq_fastLocalRankBound 181 5968 56 (by decide)]
  decide
theorem kernelA_nullity:
    coefficientCount 16688064 131071 130000 28 -
      262144 * localRankBound 92 130000 28=19682753357:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    16688064 131071 130000 28 128 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 48975840 131071 130000 81 -
      262144 * localRankBound 270 130000 81=321495185604514:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    48975840 131071 130000 81 374 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 20134512 131071 10381 33 -
      262144 * localRankBound 111 10381 33=7792307:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    20134512 131071 10381 33 154 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 32831952 131071 5968 56 -
      262144 * localRankBound 181 5968 56=786110180:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    32831952 131071 5968 56 251 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 32831952 131071 3 56 <
    coefficientCount 32831952 131071 5968 56 -
      262144 * localRankBound 181 5968 56:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedB,5964,sB⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yT,sT,LCap⟩
def chainStage:UnequalParameters:=
  ⟨n,w,agreements,yB,sB-1,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
def fixedSingularCap:ℕ:=
  CommonShearTightPrototype.countCap fixedSingular
theorem fixedSingular_exact:fixedSingularCap=7928559416753516:=by decide
theorem residualStage_exact:residualStage.regularCountCap=385018957438443:=by decide
theorem chainStage_exact:chainStage.regularCountCap=211479108682951:=by
  simpa [chainStage, LocatorChainArithmetic.chainStage, n, w, agreements,
    yB, sB, LB] using LocatorChainArithmetic.chainStage_exact
theorem tailSingular_exact:tailSingular.countCap=3253740279290:=by decide
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
def ledger:ℕ:=fixedRegularCap + fixedSingularCap +
  residualStage.regularCountCap +
  (sB - 1) * chainStage.regularCountCap + (sB + 1) * tailSingular.countCap
theorem ledger_exact:ledger=274979372324893271:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10336383
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
theorem score_radius_integer:
    (23218049:ℕ)^128 * 2^68 ≤ 33554432^128:=by decide
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      (1:ℝ≥0)/2^(68:ℕ):=by
  have hsub:(1 - radius:ℝ≥0) =23218049/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ (1:ℝ≥0)/2^(68:ℕ)
  rw [hsub,div_pow,div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6800:=by
  calc
    (1 - radius)^IRSProfile.repetitions ≤ (1:ℝ≥0)/2^(68:ℕ):=radius_power_bound
    _=claimedError 6800:=by
      unfold claimedError
      norm_num [NNReal.rpow_neg, NNReal.rpow_natCast]
end
end LocatorArithmetic
