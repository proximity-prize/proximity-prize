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
def errors:ℕ:=80575
def agreements:ℕ:=181569
def gap:ℕ:=50498
def prime:ℕ:=2130706433
def budget:ℕ:=274980725558123513
def LA:ℕ:=130000
def LB:ℕ:=7702
def LCap:ℕ:=3412
def yB:ℕ:=109
def sB:ℕ:=23
def yC:ℕ:=554
def sC:ℕ:=120
def weightedA:ℕ:=12528261
def weightedC:ℕ:=72627600
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=14343951
def weightedTCap:ℕ:=24693384
def fixedRegularCap:ℕ:=266840751749716902
theorem kernelA_rank:localRankBound 69 130000 21=5264064113:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 69 130000 21 (by decide)]
  decide +kernel
theorem kernelC_rank:localRankBound 400 130000 120=958541142020:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 400 130000 120 (by decide)]
  decide +kernel
theorem kernelB_rank:localRankBound 79 7702 23=447530160:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 79 7702 23 (by decide)]
  decide +kernel
theorem kernelTCap_rank:localRankBound 136 3412 42=1016976316:=by
  rw [LocatorRankClosed.localRankBound_eq_fast 136 3412 42 (by decide)]
  decide +kernel
theorem kernelA_nullity:
    coefficientCount 12528261 131071 130000 21 -
      262144 * localRankBound 69 130000 21=68264678009:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    12528261 131071 130000 21 96 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 72627600 131071 130000 120 -
      262144 * localRankBound 400 130000 120=1743757566946340:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    72627600 131071 130000 120 555 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 14343951 131071 7702 23 -
      262144 * localRankBound 79 7702 23=15586726:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    14343951 131071 7702 23 110 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 24693384 131071 3412 42 -
      262144 * localRankBound 136 3412 42=439223156:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    24693384 131071 3412 42 189 (by decide) (by decide)]
  decide
theorem A_ys93_quotient_upper:
    coefficientCount 207608 131071 129906 21=46855093406:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    207608 131071 129906 21 2 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 24693384 131071 0 42 <
    coefficientCount 24693384 131071 3412 42 -
      262144 * localRankBound 136 3412 42:=by
  rw [kernelTCap_nullity]
  decide
def fixedSingular:TightParameters:=⟨n,w,agreements,weightedA,3411,21⟩
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yC,sC,LA⟩
def chainStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem fixedSingular_exact:fixedSingular.countCap=1118516110467648:=by decide
theorem residualStage_exact:residualStage.regularCountCap=5258651566044150:=by decide
theorem chainStage_exact:chainStage.regularCountCap=78257955342598:=by decide
theorem tailSingular_exact:tailSingular.countCap=1713796431569:=by decide
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
theorem ledger_exact:ledger=274980725558123512:=by
  norm_num [ledger,fixedRegularCap,fixedSingular_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10313727
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
theorem score_root_integer:(2:ℕ)^82 * 47^100 ≤ 83^100:=by decide
theorem score_radius_integer:
    (23240705:ℕ)^128 * (2^67 * 83) ≤ 47 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((82:ℝ)/100) ≤ (83:ℝ≥0)/47:=by
  have hroot:((2:ℝ≥0)^(82:ℕ))^((100:ℝ)⁻¹) ≤ (83:ℝ≥0)/47:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((82:ℝ)/100) = ((2:ℝ≥0)^(82:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (47/83):=by
  have hsub:(1 - radius:ℝ≥0) =23240705/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (47/83)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6782:=by
  have hscale:(47:ℝ≥0)/83 ≤ (2:ℝ≥0)^(-((82:ℝ)/100)):=by
    calc
      (47:ℝ≥0)/83=1/((83:ℝ≥0)/47):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((82:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (47/83):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((82:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6782:=by
      unfold claimedError
      rw [show -((((6782:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((82:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
