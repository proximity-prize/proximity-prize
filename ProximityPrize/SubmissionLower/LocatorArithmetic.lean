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
def errors:ℕ:=80378
def agreements:ℕ:=181766
def gap:ℕ:=50695
def prime:ℕ:=2130706433
def budget:ℕ:=274980726511395087
def LA:ℕ:=40000
def Laux:ℕ:=40000
def LB:ℕ:=2134
def weightedA:ℕ:=9997130
def weightedAux:ℕ:=13087152
def weightedC:ℕ:=20721324
def weightedThin:ℕ:=9997130
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=17631302
def fixedRegularCap:ℕ:=272105793527427921
theorem row_values:agreements + errors = n ∧ agreements - w = gap ∧
    weightedA = 55 * agreements ∧ weightedAux = 72 * agreements ∧
    weightedC = 114 * agreements ∧ weightedB = 97 * agreements ∧ w < agreements ∧
    w + 1 ≤ weightedA ∧ weightedC < prime:=by decide
theorem kernelA_rank:localRankBound 55 40000 16 = 807376036:=by decide
theorem kernelThin_rank:localRankBound 55 40000 16 = 807376036:=by decide
theorem kernelAux_rank:localRankBound 72 40000 21 = 1778443381:=by decide
theorem kernelC_rank:localRankBound 114 40000 35 = 7153893720:=by decide
theorem kernelB_rank:localRankBound 97 2134 30 = 233637049:=by decide
theorem kernelA_nullity :
    coefficientCount 9997130 131071 40000 16 -
      262144 * localRankBound 55 40000 16 = 39308825926:=by
  rw [kernelA_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9997130 131071 40000 16 77 (by decide) (by decide)]
  decide
theorem kernelThin_nullity :
    coefficientCount 9997130 131071 40000 16 -
      262144 * localRankBound 55 40000 16 = 39308825926:=by
  rw [kernelThin_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    9997130 131071 40000 16 78 (by decide) (by decide)]
  decide
theorem kernelAux_nullity :
    coefficientCount 13087152 131071 40000 21 -
      262144 * localRankBound 72 40000 21 = 1216676258138:=by
  rw [kernelAux_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    13087152 131071 40000 21 100 (by decide) (by decide)]
  decide
theorem kernelC_nullity :
    coefficientCount 20721324 131071 40000 35 -
      262144 * localRankBound 114 40000 35 = 10544200510155:=by
  rw [kernelC_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    20721324 131071 40000 35 159 (by decide) (by decide)]
  decide
theorem kernelB_nullity :
    coefficientCount 17631302 131071 2134 30 -
      262144 * localRankBound 97 2134 30 = 56644564:=by
  rw [kernelB_rank, coefficientCount_eq_sum_range_of_weighted_cutoff
    17631302 131071 2134 30 135 (by decide) (by decide)]
  decide
theorem A_ys74_quotient_upper :
    coefficientCount 297892 131071 39926 16 = 29497040327:=by
  rw [coefficientCount_eq_sum_range_of_weighted_cutoff
    297892 131071 39926 16 3 (by decide) (by decide)]
  decide
theorem kernelA_ys74_quotient_lt (r:ℕ) (hr:r ≤ 16) :
    coefficientCount (9997130 - (74 * 131071 - r)) 131071
      (40000 - 74) (16 - r) <
    coefficientCount 9997130 131071 40000 16 -
      262144 * localRankBound 55 40000 16:=by
  rw [kernelA_nullity]
  have hmono:=RCN180.Numeric6733.coefficientCount_mono_D_s
    (D:=9997130 - (74 * 131071 - r)) (D':=297892)
    (w:=131071) (L:=39926) (s:=16 - r) (s':=16)
    (by omega) (by omega)
  rw [A_ys74_quotient_upper] at hmono
  exact hmono.trans_lt (by decide)
theorem kernelB_total_quotient_lt :
    coefficientCount 17631302 131071 0 30 <
    coefficientCount 17631302 131071 2134 30 -
      262144 * localRankBound 97 2134 30:=by
  rw [kernelB_nullity]
  decide
def fixedSingular:TightParameters:=⟨n, w, agreements, weightedA, 2133, 16⟩
def residualStage:UnequalParameters:=⟨n, w, agreements, 134, 30, LB, 158, 35, LA⟩
def residualSingular:TightParameters:=⟨n, w, agreements, weightedB, LB, 30⟩
theorem fixedSingular_exact:fixedSingular.countCap = 317847064806400:=by decide
theorem residualStage_exact:residualStage.regularCountCap = 525379395734196:=by decide
theorem residualSingular_exact:residualSingular.countCap = 2031706523426568:=by decide
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
theorem ledger_exact:ledger = 274980726511395086:=by
  rw [ledger, fixedRegularCap, fixedSingular_exact,
    residualStage_exact, residualSingular_exact]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10288450
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
theorem score_root_integer:(2:ℕ)^62 * 1000000000^100 ≤ 1536875182^100:=by decide
theorem score_radius_integer :
    (23265982:ℕ)^128 * (2^67 * 1536875182) ≤ 1000000000 * 33554432^128:=by decide
theorem two_rpow_fraction_le :
    (2:ℝ≥0)^((62:ℝ)/100) ≤ (1536875182:ℝ≥0)/1000000000:=by
  have hroot:((2:ℝ≥0)^(62:ℕ))^((100:ℝ)⁻¹) ≤ (1536875182:ℝ≥0)/1000000000:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((62:ℝ)/100) = ((2:ℝ≥0)^(62:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound :
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1536875182):=by
  have hsub:(1 - radius:ℝ≥0) = 23265982/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1536875182)
  rw [hsub, div_pow, div_mul_div_comm, one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le :
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6762:=by
  have hscale:(1000000000:ℝ≥0)/1536875182 ≤ (2:ℝ≥0)^(-((62:ℝ)/100)):=by
    calc
      (1000000000:ℝ≥0)/1536875182 = 1/((1536875182:ℝ≥0)/1000000000):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((62:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _ = _:=by rw [one_div, NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(67:ℕ)) * (1000000000/1536875182):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(67:ℕ)) * (2:ℝ≥0)^(-((62:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6762:=by
      unfold claimedError
      rw [show -((((6762:ℕ):ℝ)/100)) =
          -((67:ℕ):ℝ) + -((62:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.LocatorArithmetic
