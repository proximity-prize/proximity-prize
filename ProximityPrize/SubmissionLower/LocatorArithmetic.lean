import ProximityPrize.SubmissionLower.LocatorChainArithmetic

/-! Packed from ProximityPrize.SubmissionLower.LocatorArithmetic. -/
section PackedLocator_LocatorArithmetic
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
def errors:ℕ:=80771
def agreements:ℕ:=181373
def gap:ℕ:=50302
def prime:ℕ:=2130706433
def budget:ℕ:=274980723107224037
def LA:ℕ:=130000
def LB:ℕ:=12960
def LCap:ℕ:=6415
def yB:ℕ:=153
def sB:ℕ:=33
def yC:ℕ:=373
def sC:ℕ:=81
def yT:ℕ:=250
def sT:ℕ:=56
def weightedA:ℕ:=17411808
def weightedC:ℕ:=48970710
abbrev weightedAmbient:=weightedC
def weightedB:ℕ:=20132403
def weightedTCap:ℕ:=32828513
def fixedRegularCap:ℕ:=254595720129422441
theorem kernelA_rank:localRankBound 96 130000 29=13837332645:=by
  rw [localRankBound_eq_fastLocalRankBound 96 130000 29 (by decide)]
  decide
theorem kernelC_rank:localRankBound 270 130000 81=296615133081:=by
  rw [localRankBound_eq_fastLocalRankBound 270 130000 81 (by decide)]
  decide
theorem kernelB_rank:localRankBound 111 12960 33=2086613235:=by
  rw [localRankBound_eq_fastLocalRankBound 111 12960 33 (by decide)]
  decide
theorem kernelTCap_rank:localRankBound 181 6415 56=4498479216:=by
  rw [localRankBound_eq_fastLocalRankBound 181 6415 56 (by decide)]
  decide
theorem kernelA_nullity:
    coefficientCount 17411808 131071 130000 29 -
      262144 * localRankBound 96 130000 29=122788671575:=by
  rw [kernelA_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    17411808 131071 130000 29 133 (by decide) (by decide)]
  decide
theorem kernelC_nullity:
    coefficientCount 48970710 131071 130000 81 -
      262144 * localRankBound 270 130000 81=303286218157264:=by
  rw [kernelC_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    48970710 131071 130000 81 374 (by decide) (by decide)]
  decide
theorem kernelB_nullity:
    coefficientCount 20132403 131071 12960 33 -
      262144 * localRankBound 111 12960 33=35582615:=by
  rw [kernelB_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    20132403 131071 12960 33 154 (by decide) (by decide)]
  decide
theorem kernelTCap_nullity:
    coefficientCount 32828513 131071 6415 56 -
      262144 * localRankBound 181 6415 56=505596574:=by
  rw [kernelTCap_rank,coefficientCount_eq_sum_range_of_weighted_cutoff
    32828513 131071 6415 56 251 (by decide) (by decide)]
  decide
theorem kernelTCap_total_quotient_lt:
    coefficientCount 32828513 131071 2 56 <
    coefficientCount 32828513 131071 6415 56 -
      262144 * localRankBound 181 6415 56:=by
  rw [kernelTCap_nullity]
  decide
/-- Fixed-stage derivative chain (`LocatorFixedChain.fixed_chain_count_le` with
`T := H`): the differentiated left factor has slope at most `sB - 1 = 32`
(`LocatorDerivativeChain.chainSeeds_card_le`), the original factor on the right
slope `33`; both sides live in the wide selected box `(6412,153,33)`. -/
def chainH:UnequalParameters:=⟨n,w,agreements,yB,sB - 1,6412,yB,sB,6412⟩
/-- Fixed-stage slope-free tails (the `R`-free ends of the chains and the
`R`-free product), in the wide box at slope `1`. -/
def tailH:TightParameters:=⟨n,w,agreements,weightedB,6412,1⟩
/-- What the fixed stage charges besides the certified regular maximum:
`32` chain stages and `34` tail slots.  Replaces the singular-seed count of the
whole gcd (`CommonShearTightPrototype.countCap ⟨n,w,agreements,weightedB,6412,sB⟩
= 8526521187049187`). -/
def fixedChainCap:ℕ:=(sB - 1) * chainH.regularCountCap + (sB + 1) * tailH.countCap
def residualStage:UnequalParameters:=⟨n,w,agreements,yB,sB,LB,yT,sT,LCap⟩
def chainStage:UnequalParameters:=
  ⟨n,w,agreements,yB,sB-1,LB,yB,sB,LB⟩
def tailSingular:TightParameters:=⟨n,w,agreements,weightedB,LB,1⟩
theorem chainH_exact:chainH.regularCountCap=130673289699937:=by decide
theorem tailH_exact:tailH.countCap=2010440530563:=by decide
theorem fixedChainCap_exact:fixedChainCap=4249900248437126:=by
  norm_num [fixedChainCap,chainH_exact,tailH_exact,sB]
theorem residualStage_exact:residualStage.regularCountCap=469008854116807:=by decide
theorem chainStage_exact:chainStage.regularCountCap=264117369694349:=by
  simpa [chainStage, LocatorChainArithmetic.chainStage, n, w, agreements,
    yB, sB, LB] using LocatorChainArithmetic.chainStage_exact
theorem tailSingular_exact:tailSingular.countCap=4063680072343:=by decide
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
theorem tailH_gates:SingularGates tailH:=by constructor <;> decide
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
def ledger:ℕ:=fixedRegularCap + fixedChainCap +
  residualStage.regularCountCap +
  (sB - 1) * chainStage.regularCountCap + (sB + 1) * tailSingular.countCap
theorem ledger_exact:ledger=267904550184655204:=by
  norm_num [ledger,fixedRegularCap,fixedChainCap_exact,
    residualStage_exact,chainStage_exact,tailSingular_exact,sB]
theorem ledger_lt:ledger < budget:=by rw [ledger_exact]; decide
def radiusNumerator:ℕ:=10338815
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
theorem score_root_integer:(2:ℕ)^2 * 71^100 ≤ 72^100:=by decide
theorem score_radius_integer:
    (23215617:ℕ)^128 * (2^68 * 72) ≤ 71 * 33554432^128:=by decide
theorem two_rpow_fraction_le:
    (2:ℝ≥0)^((2:ℝ)/100) ≤ (72:ℝ≥0)/71:=by
  have hroot:((2:ℝ≥0)^(2:ℕ))^((100:ℝ)⁻¹) ≤ (72:ℝ≥0)/71:=by
    rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
    rw [NNReal.rpow_ofNat,div_pow,le_div_iff₀ (by positivity)]
    exact_mod_cast score_root_integer
  calc
    (2:ℝ≥0)^((2:ℝ)/100) = ((2:ℝ≥0)^(2:ℕ))^((100:ℝ)⁻¹):=by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ _:=hroot
theorem radius_power_bound:
    (1 - radius)^IRSProfile.repetitions ≤
      ((1:ℝ≥0)/2^(68:ℕ)) * (71/72):=by
  have hsub:(1 - radius:ℝ≥0) =23215617/33554432:=by
    have hr:radius ≤ 1:=by
      rw [← NNReal.coe_le_coe]
      norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
    apply NNReal.coe_injective
    rw [NNReal.coe_sub hr]
    norm_num [radius,claimedRadius,radiusNumerator,radiusDenominator]
  change (1 - radius)^128 ≤ ((1:ℝ≥0)/2^(68:ℕ)) * (71/72)
  rw [hsub,div_pow,div_mul_div_comm,one_mul,
    div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast score_radius_integer
theorem score_target_le:
    (1 - radius)^IRSProfile.repetitions ≤ claimedError 6802:=by
  have hscale:(71:ℝ≥0)/72 ≤ (2:ℝ≥0)^(-((2:ℝ)/100)):=by
    calc
      (71:ℝ≥0)/72=1/((72:ℝ≥0)/71):=by norm_num
      _ ≤ 1/((2:ℝ≥0)^((2:ℝ)/100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_fraction_le
      _=_:=by rw [one_div,NNReal.rpow_neg]
  calc
    (1 - radius)^IRSProfile.repetitions ≤
        ((1:ℝ≥0)/2^(68:ℕ)) * (71/72):=radius_power_bound
    _ ≤ ((1:ℝ≥0)/2^(68:ℕ)) * (2:ℝ≥0)^(-((2:ℝ)/100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _=claimedError 6802:=by
      unfold claimedError
      rw [show -((((6802:ℕ):ℝ)/100)) =
          -((68:ℕ):ℝ) + -((2:ℝ)/100) by norm_num,
        NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg,NNReal.rpow_natCast,one_div]
end
end LocatorArithmetic
end ProximityPrize.SubmissionLower
end PackedLocator_LocatorArithmetic

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier29 : True := by trivial
end ProximityPrize.SubmissionLower

