import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorRankClosed
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
def errors:ℕ:=80604
def agreements:ℕ:=181540
def gap:ℕ:=50469
def prime:ℕ:=2130706433
def budget:ℕ:=274980725314288096
def LA:ℕ:=130000
def LAux:ℕ:=130000
def LB:ℕ:=8400
def LC:ℕ:=130000
def LCap:ℕ:=3700
def yAux:ℕ:=102
def sAux:ℕ:=22
def yB:ℕ:=116
def sB:ℕ:=24
def yC:ℕ:=554
def sC:ℕ:=120
def weightedA:ℕ:=13433960
def weightedAux:ℕ:=13433960
def weightedC:ℕ:=72616000
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=15249360
def weightedTCap:ℕ:=25778680
def fixedRegularCap:ℕ:=265877011283886055
theorem kernelA_rank:localRankBound 74 130000 21=6143238453:=by
  rw [← LocatorKernelEval.localRankBound_eq 74 130000 21 (by decide)]
  decide
theorem kernelC_rank:localRankBound 400 130000 120=958541142020:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 400 130000 120 (by decide)]
  decide
theorem kernelB_rank:localRankBound 84 8400 24=576726900:=by
  rw [← LocatorKernelEval.localRankBound_eq 84 8400 24 (by decide)]
  decide
theorem kernelTCap_rank:localRankBound 142 3700 44=1257416820:=by
  rw [← LocatorKernelEval.localRankBound_eq 142 3700 44 (by decide)]
  decide
theorem kernelA_nullity:
    coefficientCount 13433960 131071 130000 21 -
      262144 * localRankBound 74 130000 21=141959952266:=by
  rw [kernelA_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    13433960 131071 130000 21 103 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 72616000 131071 130000 120 -
      262144 * localRankBound 400 130000 120=1653647654042340:=by
  rw [kernelC_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    72616000 131071 130000 120 555 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 15249360 131071 8400 24 -
      262144 * localRankBound 84 8400 24=903742550:=by
  rw [kernelB_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    15249360 131071 8400 24 117 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 25778680 131071 3700 44 -
      262144 * localRankBound 142 3700 44=360692415:=by
  rw [kernelTCap_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    25778680 131071 3700 44 197 (by decide) (by decide)]
  decide
theorem A_ys95_quotient_upper:
    coefficientCount 326881 131071 129900 21=118562720461:=by
  rw [LocatorKernelEval.coefficientCount_eq_cutoff
    326881 131071 129900 21 3 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 25778680 131071 2 44 <
    coefficientCount 25778680 131071 3700 44 -
      262144 * localRankBound 142 3700 44:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,3697,21⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yC,sC,LC⟩
def chainStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem fixedSingular_exact:fixedSingular.countCap=1300921862639790:=by decide
theorem residualStage_exact:residualStage.regularCountCap=5571167482229417:=by decide
theorem chainStage_exact:chainStage.regularCountCap=94863800761446:=by decide
theorem tailSingular_exact:tailSingular.countCap=1990290720783:=by decide
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
theorem ledger_exact:ledger=274980725314288095:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10317410
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
theorem score_root_integer:(2:ℕ)^17 * 719^20 ≤ 1296^20:=by decide
theorem score_radius_integer:
    (23237022:ℕ)^128 * (2^67 * 1296) ≤ 719 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((17:ℝ)/20) ≤ (1296:ℝ≥0)/719:=by
  have hroot:((2:ℝ≥0)^(17:ℕ))^((20:ℝ)⁻¹) ≤ (1296:ℝ≥0)/719:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 20)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((17:ℝ)/20) = ((2:ℝ≥0)^(17:ℕ))^((20:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (719/1296):=by
  have hsub:(1 - radius:ℝ≥0) =23237022/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (719/1296)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6785:=by
  have hscale:(719:ℝ≥0)/1296 ≤ (2:ℝ≥0)^(-((17:ℝ)/20)):=by
    calc
      (719:ℝ≥0)/1296=1/((1296:ℝ≥0)/719):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((17:ℝ)/20)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (719/1296):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((17:ℝ)/20)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6785:=by
      unfold claimedError
      rw [show -((((6785:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((17:ℝ)/20) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
