import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
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
/-! Row 6787: errors 80624, agreements 181520.  The selected pair is drawn from
the total-cap kernel `TCap = (145, 3923, 45)` and the B kernel `(80, 16000, 23)`;
the A kernel `(76, 130000, 22)` only supplies the per-factor ys/slope caps of the
narrow grid, and the C kernel `(400, 130000, 120)` is a route source. -/
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80624
def agreements:ℕ:=181520
def gap:ℕ:=50449
def prime:ℕ:=2130706433
def budget:ℕ:=274980725030190606
def LA:ℕ:=130000
def LB:ℕ:=16000
def LC:ℕ:=130000
def LCap:ℕ:=3923
def yA:ℕ:=105
def sA:ℕ:=22
def yB:ℕ:=110
def sB:ℕ:=23
def yC:ℕ:=553
def sC:ℕ:=120
def yT:ℕ:=200
def sT:ℕ:=45
def weightedA:ℕ:=13795520
def weightedC:ℕ:=72608000
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=14521600
def weightedTCap:ℕ:=26320400
def fixedRegularCap:ℕ:=269159312872668139
theorem kernelA_rank:localRankBound 76 130000 22=6740780706:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 76 130000 22 (by decide)]
  decide +kernel
theorem kernelAux_rank:localRankBound 76 130000 23=6962613720:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 76 130000 23 (by decide)]
  decide +kernel
theorem kernelC_rank:localRankBound 400 130000 120=958541142020:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 400 130000 120 (by decide)]
  decide +kernel
theorem kernelB_rank:localRankBound 80 16000 23=958030968:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 80 16000 23 (by decide)]
  decide +kernel
theorem kernelTCap_rank:localRankBound 145 3923 45=1421071215:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 145 3923 45 (by decide)]
  decide +kernel
theorem kernelA_nullity:
    coefficientCount 13795520 131071 130000 22 -
      262144 * localRankBound 76 130000 22=255124945551:=by
  rw [kernelA_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    13795520 131071 130000 22 106 (by decide) (by decide)]
  decide
theorem kernelAux_nullity:
    coefficientCount 13795520 131071 130000 23 -
      262144 * localRankBound 76 130000 23=422421820346:=by
  rw [kernelAux_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    13795520 131071 130000 23 106 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 72608000 131071 130000 120 -
      262144 * localRankBound 400 130000 120=1591585493643178:=by
  rw [kernelC_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    72608000 131071 130000 120 554 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 14521600 131071 16000 23 -
      262144 * localRankBound 80 16000 23=986249694:=by
  rw [kernelB_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    14521600 131071 16000 23 111 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 26320400 131071 3923 45 -
      262144 * localRankBound 145 3923 45=221696885:=by
  rw [kernelTCap_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    26320400 131071 3923 45 201 (by decide) (by decide)]
  decide
/-- The quotient box of an A-kernel reconstruction by a divisor of ys weight at
least `102`: contact weight at most `13795520 - 13369220 = 426300`, length
`129898`, slope `22`.  Its dimension is below the A nullity, so no divisor of
ys weight `102` or more divides every reconstruction. -/
theorem A_ys101_quotient_upper:
    coefficientCount 426300 131071 129898 22=213238926935:=by
  rw [LocatorKernelEval.coefficientCount_eq_cutoff
    426300 131071 129898 22 4 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 26320400 131071 0 45 <
    coefficientCount 26320400 131071 3923 45 -
      262144 * localRankBound 145 3923 45:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedB,3922,sB⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yT,sT,LCap⟩
def chainStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem fixedSingular_exact:fixedSingular.countCap=1797707184418499:=by decide
theorem residualStage_exact:residualStage.regularCountCap=324499950147213:=by decide
theorem chainStage_exact:chainStage.regularCountCap=164222101394339:=by decide
theorem tailSingular_exact:tailSingular.countCap=3596616345054:=by decide
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
theorem ledger_exact:ledger=274980725030190605:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10319999
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
theorem score_root_integer:(2:ℕ)^87 * 64^100 ≤ 117^100:=by decide
theorem score_radius_integer:
    (23234433:ℕ)^128 * (2^67 * 117) ≤ 64 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((87:ℝ)/100) ≤ (117:ℝ≥0)/64:=by
  have hroot:((2:ℝ≥0)^(87:ℕ))^((100:ℝ)⁻¹) ≤ (117:ℝ≥0)/64:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((87:ℝ)/100) = ((2:ℝ≥0)^(87:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (64/117):=by
  have hsub:(1 - radius:ℝ≥0) =23234433/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (64/117)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6787:=by
  have hscale:(64:ℝ≥0)/117 ≤ (2:ℝ≥0)^(-((87:ℝ)/100)):=by
    calc
      (64:ℝ≥0)/117=1/((117:ℝ≥0)/64):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((87:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (64/117):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((87:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6787:=by
      unfold claimedError
      rw [show -((((6787:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((87:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
