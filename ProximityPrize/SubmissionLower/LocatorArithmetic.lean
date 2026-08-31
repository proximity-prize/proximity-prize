import ProximityPrize.SubmissionLower.L1
import ProximityPrize.SubmissionLower.N5
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.Z8
import ProximityPrize.SubmissionLower.D1
namespace ProximityPrize.SubmissionLower.LocatorArithmetic
open ProximityPrize.Benchmark
open scoped BigOperators NNReal
open RCN100 RCN119 RCN302
open RCN318 RCN260
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
def n:ℕ:=262144
def w:ℕ:=131071
def errors:ℕ:=80368
def agreements:ℕ:=181776
def gap:ℕ:=50705
def prime:ℕ:=2130706433
def budget:ℕ:=274980726611395087
def LA:ℕ:=40000
def Laux:ℕ:=40000
def LB:ℕ:=2082
def weightedA:ℕ:=9815904
def weightedAux:ℕ:=13087872
def weightedC:ℕ:=18541152
def weightedThin:ℕ:=9815904
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=17995824
def fixedRegularCap:ℕ:=272036573261625803
theorem row_values:agreements + errors = n ∧ agreements - w = gap ∧
    weightedA = 54 * agreements ∧ weightedAux = 72 * agreements ∧
    weightedC = 102 * agreements ∧ weightedB = 99 * agreements ∧ w < agreements ∧
    w + 1 ≤ weightedA ∧ weightedC < prime:=by decide
theorem kernelA_rank:localRankBound 54 40000 16 = 775440618:=by decide
theorem kernelThin_rank:localRankBound 54 40000 16 = 775440618:=by decide
theorem kernelAux_rank:localRankBound 72 40000 21 = 1778443381:=by decide
theorem kernelC_rank:localRankBound 102 40000 31 = 5111141216:=by decide
theorem kernelB_rank:localRankBound 99 2082 31 = 244059712:=by decide
theorem kernelA_nullity :
    coefficientCount 9815904 131071 40000 16 -
      262144 * localRankBound 54 40000 16 = 25068190378:=by
  rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9815904 131071 40000 16 75 (by decide) (by decide)]
  decide
theorem kernelThin_nullity :
    coefficientCount 9815904 131071 40000 16 -
      262144 * localRankBound 54 40000 16 = 25068190378:=by
  rw [kernelThin_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9815904 131071 40000 16 78 (by decide) (by decide)]
  decide
theorem kernelAux_nullity :
    coefficientCount 13087872 131071 40000 21 -
      262144 * localRankBound 72 40000 21 = 1273307576618:=by
  rw [kernelAux_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13087872 131071 40000 21 100 (by decide) (by decide)]
  decide
theorem kernelC_nullity :
    coefficientCount 18541152 131071 40000 31 -
      262144 * localRankBound 102 40000 31 = 6917788416568:=by
  rw [kernelC_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    18541152 131071 40000 31 142 (by decide) (by decide)]
  decide
theorem kernelB_nullity :
    coefficientCount 17995824 131071 2082 31 -
      262144 * localRankBound 99 2082 31 = 123520888:=by
  rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    17995824 131071 2082 31 138 (by decide) (by decide)]
  decide
theorem A_ys73_quotient_upper :
    coefficientCount 247737 131071 39927 16 = 19207929627:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    247737 131071 39927 16 3 (by decide) (by decide)]
  decide
theorem kernelA_ys73_quotient_lt (r:ℕ) (hr:r ≤ 16) :
    coefficientCount (9815904 - (73 * 131071 - r)) 131071
      (40000 - 73) (16 - r) <
    coefficientCount 9815904 131071 40000 16 -
      262144 * localRankBound 54 40000 16:=by
  rw [kernelA_nullity]
  have hmono:=RCN180.Numeric6733.coefficientCount_mono_D_s
    (D:=9815904 - (73 * 131071 - r)) (D':=247737)
    (w:=131071) (L:=39927) (s:=16 - r) (s':=16)
    (by omega) (by omega)
  rw [A_ys73_quotient_upper] at hmono
  exact hmono.trans_lt (by decide)
theorem kernelB_total_quotient_lt :
    coefficientCount 17995824 131071 1 31 <
    coefficientCount 17995824 131071 2082 31 -
      262144 * localRankBound 99 2082 31:=by
  rw [kernelB_nullity]
  decide
def fixedSingular:TightParameters:=⟨n, w, agreements, weightedA, 2080, 16⟩
def residualStage:UnequalParameters:=⟨n, w, agreements, 137, 31, LB, 141, 31, LA⟩
def residualSingular:TightParameters:=⟨n, w, agreements, weightedB, LB, 31⟩
theorem fixedSingular_exact:fixedSingular.countCap = 304251425222668:=by decide
theorem residualStage_exact:residualStage.regularCountCap = 477570269371354:=by decide
theorem residualSingular_exact:residualSingular.countCap = 2162331655175260:=by decide
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
theorem fixed_singular_gates:SingularGates fixedSingular:=by constructor <;> decide
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
  residualStage.regularCountCap + residualSingular.countCap + 1
theorem ledger_exact:ledger = 274980726611395086:=by
  rw [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10287190
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
theorem radius_floor :
    ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ = errors:=by
  norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    errors, IRSProfile.Index]
theorem radius_admissible :
    radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
  constructor <;> norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
    IRSProfile.minRelativeDistance]
theorem score_root_integer:(2:ℕ)^61 * 1000000000^100 ≤ 1526259209^100:=by decide
theorem score_radius_integer :
    (23267242:ℕ)^128 * (2^67 * 1526259209) ≤ 1000000000 * 33554432^128:=by decide
theorem two_rpow_fraction_le :
    (2:ℝ≥0)^((61:ℝ)/100) ≤ (1526259209:ℝ≥0)/1000000000:=by
  have hroot:((2:ℝ≥0)^(61:ℕ))^((100:ℝ)⁻¹) ≤ (1526259209:ℝ≥0)/1000000000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((61:ℝ)/100) = ((2:ℝ≥0)^(61:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1526259209):=by
  have hsub:(1 - radius:ℝ≥0) = 23267242/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1526259209)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6761:=by
  have hscale:(1000000000:ℝ≥0)/1526259209 ≤ (2:ℝ≥0)^(-((61:ℝ)/100)):=by
    calc
      (1000000000:ℝ≥0)/1526259209 = 1/((1526259209:ℝ≥0)/1000000000):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((61:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _:=by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1526259209):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((61:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6761:=by
      unfold claimedError
      rw [show -((((6761:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((61:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.LocatorArithmetic
