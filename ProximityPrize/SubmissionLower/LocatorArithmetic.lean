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
/-! Row 6786: errors 80614, agreements 181530.  The selected pair is drawn from
the total-cap kernel `TCap = (142, 3809, 44)` and the B kernel `(82, 9600, 24)`;
the A kernel `(75, 130000, 22)` only supplies the per-factor ys/slope caps of the
narrow grid, and the C kernel `(400, 130000, 120)` is a route source. -/
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80614
def agreements:ℕ:=181530
def gap:ℕ:=50459
def prime:ℕ:=2130706433
def budget:ℕ:=274980725090043428
def LA:ℕ:=130000
def LB:ℕ:=9600
def LC:ℕ:=130000
def LCap:ℕ:=3809
def yA:ℕ:=103
def sA:ℕ:=22
def yB:ℕ:=113
def sB:ℕ:=24
def yC:ℕ:=553
def sC:ℕ:=120
def yT:ℕ:=196
def sT:ℕ:=44
def weightedA:ℕ:=13614750
def weightedC:ℕ:=72612000
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=14885460
def weightedTCap:ℕ:=25777260
def fixedRegularCap:ℕ:=270344084085901085
theorem kernelA_rank:localRankBound 75 130000 22=6546495014:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 75 130000 22 (by decide)]
  decide +kernel
theorem kernelAux_rank:localRankBound 75 130000 23=6761440848:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 75 130000 23 (by decide)]
  decide +kernel
theorem kernelC_rank:localRankBound 400 130000 120=958541142020:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 400 130000 120 (by decide)]
  decide +kernel
theorem kernelB_rank:localRankBound 82 9600 24=625316150:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 82 9600 24 (by decide)]
  decide +kernel
theorem kernelTCap_rank:localRankBound 142 3809 44=1295095395:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 142 3809 44 (by decide)]
  decide +kernel
theorem kernelA_nullity:
    coefficientCount 13614750 131071 130000 22 -
      262144 * localRankBound 75 130000 22=351572585294:=by
  rw [kernelA_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    13614750 131071 130000 22 104 (by decide) (by decide)]
  decide
theorem kernelAux_nullity:
    coefficientCount 13614750 131071 130000 23 -
      262144 * localRankBound 75 130000 23=396080340478:=by
  rw [kernelAux_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    13614750 131071 130000 23 104 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 72612000 131071 130000 120 -
      262144 * localRankBound 400 130000 120=1622595225055178:=by
  rw [kernelC_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    72612000 131071 130000 120 554 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 14885460 131071 9600 24 -
      262144 * localRankBound 82 9600 24=556469350:=by
  rw [kernelB_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    14885460 131071 9600 24 114 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 25777260 131071 3809 44 -
      262144 * localRankBound 142 3809 44=387593535:=by
  rw [kernelTCap_rank,LocatorKernelEval.coefficientCount_eq_cutoff
    25777260 131071 3809 44 197 (by decide) (by decide)]
  decide
/-- The quotient box of an A-kernel reconstruction by a divisor of ys weight at
least `100`: contact weight at most `13614750 - 13107078 = 507672`, length
`129900`, slope `22`.  Its dimension is below the A nullity, so no divisor of
ys weight `100` or more divides every reconstruction. -/
theorem A_ys99_quotient_upper:
    coefficientCount 507672 131071 129900 22=318943624395:=by
  rw [LocatorKernelEval.coefficientCount_eq_cutoff
    507672 131071 129900 22 4 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 25777260 131071 0 44 <
    coefficientCount 25777260 131071 3809 44 -
      262144 * localRankBound 142 3809 44:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedB,3808,sB⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yT,sT,LCap⟩
def chainStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem fixedSingular_exact:fixedSingular.countCap=1951366380128901:=by decide
theorem residualStage_exact:residualStage.regularCountCap=200314178430427:=by decide
theorem chainStage_exact:chainStage.regularCountCap=105632783889043:=by decide
theorem tailSingular_exact:tailSingular.countCap=2216256645401:=by decide
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
theorem ledger_exact:ledger=274980725090043427:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10318719
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
theorem score_root_integer:(2:ℕ)^86 * 65^100 ≤ 118^100:=by decide
theorem score_radius_integer:
    (23235713:ℕ)^128 * (2^67 * 118) ≤ 65 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((86:ℝ)/100) ≤ (118:ℝ≥0)/65:=by
  have hroot:((2:ℝ≥0)^(86:ℕ))^((100:ℝ)⁻¹) ≤ (118:ℝ≥0)/65:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((86:ℝ)/100) = ((2:ℝ≥0)^(86:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (65/118):=by
  have hsub:(1 - radius:ℝ≥0) =23235713/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (65/118)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6786:=by
  have hscale:(65:ℝ≥0)/118 ≤ (2:ℝ≥0)^(-((86:ℝ)/100)):=by
    calc
      (65:ℝ≥0)/118=1/((118:ℝ≥0)/65):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((86:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (65/118):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((86:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6786:=by
      unfold claimedError
      rw [show -((((6786:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((86:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
