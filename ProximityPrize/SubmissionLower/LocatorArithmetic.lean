import ProximityPrize.SubmissionLower.LocatorRankClosed
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
def errors:ℕ:=80614
def agreements:ℕ:=181530
def gap:ℕ:=50459
def prime:ℕ:=2130706433
def budget:ℕ:=274980725228956150
def LA:ℕ:=278867
def LAux:ℕ:=89400
def LC:ℕ:=278867
def LB:ℕ:=7742
def LCap:ℕ:=3809
def yB:ℕ:=117
def sB:ℕ:=25
def yC:ℕ:=394
def sC:ℕ:=85
def weightedA:ℕ:=13433220
def weightedC:ℕ:=51736050
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=15430050
def weightedTCap:ℕ:=25777260
def fixedRegularCap:ℕ:=263528531609206492
theorem kernelA_rank:localRankBound 74 278867 21=13179734942:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 74 278867 21 (by decide)]
  decide +kernel
theorem kernelC_rank:localRankBound 285 130000 85=346972180425:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 285 130000 85 (by decide)]
  decide +kernel
theorem kernelB_rank:localRankBound 85 7742 25=561976025:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 85 7742 25 (by decide)]
  decide +kernel
theorem kernelTCap_rank:localRankBound 142 3809 44=1295095395:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 142 3809 44 (by decide)]
  decide +kernel
theorem kernelA_nullity:
    coefficientCount 13433220 131071 278867 21 -
      262144 * localRankBound 74 278867 21=139502:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    13433220 131071 278867 21 103 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 51736050 131071 130000 85 -
      262144 * localRankBound 285 130000 85=538299882917330:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    51736050 131071 130000 85 395 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 15430050 131071 7742 25 -
      262144 * localRankBound 85 7742 25=10725676:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    15430050 131071 7742 25 118 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 25777260 131071 3809 44 -
      262144 * localRankBound 142 3809 44=387593535:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    25777260 131071 3809 44 197 (by decide) (by decide)]
  decide
theorem A_ys102_quotient_upper:
    coefficientCount 0 131071 278764 21=0:=by
  simp [coefficientCount]
theorem kernelTCap_total_quotient_lt:
    coefficientCount 25777260 131071 2 44 <
    coefficientCount 25777260 131071 3809 44 -
      262144 * localRankBound 142 3809 44:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,3806,21⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yC,sC,LC⟩
def chainStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem fixedSingular_exact:fixedSingular.countCap=1339544210897973:=by decide
theorem residualStage_exact:residualStage.regularCountCap=7858817027618416:=by decide
theorem chainStage_exact:chainStage.regularCountCap=91904915338130:=by decide
theorem tailSingular_exact:tailSingular.countCap=1850554350698:=by decide
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
theorem ledger_exact:ledger=274980725228956149:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10318668
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
theorem score_root_integer:(2:ℕ)^86 * 1822^100 ≤ 3307^100:=by decide
theorem score_radius_integer:
    (23235764:ℕ)^128 * (2^67 * 3307) ≤ 1822 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((86:ℝ)/100) ≤ (3307:ℝ≥0)/1822:=by
  have hroot:((2:ℝ≥0)^(86:ℕ))^((100:ℝ)⁻¹) ≤ (3307:ℝ≥0)/1822:=by
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
      ((1:ℝ≥0)/2^(67:ℕ)) * (1822/3307):=by
  have hsub:(1 - radius:ℝ≥0) =23235764/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (1822/3307)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6786:=by
  have hscale:(1822:ℝ≥0)/3307 ≤ (2:ℝ≥0)^(-((86:ℝ)/100)):=by
    calc
      (1822:ℝ≥0)/3307=1/((3307:ℝ≥0)/1822):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((86:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (1822/3307):=radius_power_bound
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
