import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
import ProximityPrize.SubmissionLower.LocatorKernelEval
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
def errors:ℕ:=80585
def agreements:ℕ:=181559
def gap:ℕ:=50488
def prime:ℕ:=2130706433
def budget:ℕ:=274980725476972198
def LA:ℕ:=130000
def LB:ℕ:=6959
def LCap:ℕ:=3506
def yB:ℕ:=113
def sB:ℕ:=24
def yC:ℕ:=394
def sC:ℕ:=85
def weightedA:ℕ:=12709130
def weightedC:ℕ:=51744315
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=14887838
def weightedTCap:ℕ:=25236701
def fixedRegularCap:ℕ:=268330452984175476
theorem kernelA_rank:localRankBound 70 130000 21=5434182061:=by
  rw [← LocatorKernelEval.localRankBound_eq 70 130000 21 (by decide)]
  decide
theorem kernelC_rank:localRankBound 285 130000 85=346972180425:=by
  rw [← LocatorKernelEval.localRankBound_eq 285 130000 85 (by decide)]
  decide
theorem kernelB_rank:localRankBound 82 6959 24=452660775:=by
  rw [← LocatorKernelEval.localRankBound_eq 82 6959 24 (by decide)]
  decide
theorem kernelTCap_rank:localRankBound 139 3506 43=1116368660:=by
  rw [← LocatorKernelEval.localRankBound_eq 139 3506 43 (by decide)]
  decide
theorem kernelA_nullity:
    coefficientCount 12709130 131071 130000 21 -
      262144 * localRankBound 70 130000 21=44259914061:=by
  rw [kernelA_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    12709130 131071 130000 21 97 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 51744315 131071 130000 85 -
      262144 * localRankBound 285 130000 85=570817620937055:=by
  rw [kernelC_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    51744315 131071 130000 85 395 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 14887838 131071 6959 24 -
      262144 * localRankBound 82 6959 24=12023475:=by
  rw [kernelB_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    14887838 131071 6959 24 114 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 25236701 131071 3506 43 -
      262144 * localRankBound 139 3506 43=113976093:=by
  rw [kernelTCap_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    25236701 131071 3506 43 193 (by decide) (by decide)]
  decide
theorem A_ys95_quotient_upper:
    coefficientCount 126335 131071 129904 0=16411548175:=by
  rw [LocatorKernelEval.coefficientCount_eq_cutoff
    126335 131071 129904 0 1 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 25236701 131071 1 43 <
    coefficientCount 25236701 131071 3506 43 -
      262144 * localRankBound 139 3506 43:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,3504,21⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yC,sC,LA⟩
def chainStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem fixedSingular_exact:fixedSingular.countCap=1165959641757253:=by decide
theorem residualStage_exact:residualStage.regularCountCap=3684008142324131:=by decide
theorem chainStage_exact:chainStage.regularCountCap=76528902293844:=by decide
theorem tailSingular_exact:tailSingular.countCap=1605598238277:=by decide
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
theorem ledger_exact:ledger=274980725476972197:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10314893
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
theorem score_root_integer:
    (2:ℕ)^83 * 500000^100 ≤ 888843^100:=by decide
theorem score_radius_integer:
    (23239539:ℕ)^128 * (2^67 * 888843) ≤
      500000 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((83:ℝ)/100) ≤ (888843:ℝ≥0)/500000:=by
  have hroot:((2:ℝ≥0)^(83:ℕ))^((100:ℝ)⁻¹) ≤
      (888843:ℝ≥0)/500000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((83:ℝ)/100) =
        ((2:ℝ≥0)^(83:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (500000/888843):=by
  have hsub:(1 - radius:ℝ≥0) =23239539/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (500000/888843)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6783:=by
  have hscale:(500000:ℝ≥0)/888843 ≤
      (2:ℝ≥0)^(-((83:ℝ)/100)):=by
    calc
      (500000:ℝ≥0)/888843=1/((888843:ℝ≥0)/500000):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((83:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (500000/888843):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((83:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6783:=by
      unfold claimedError
      rw [show -((((6783:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((83:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
