import ProximityPrize.SubmissionLower.CJ
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.D1
import ProximityPrize.SubmissionLower.Z8
namespace ProximityPrize.SubmissionLower.RCN327
open ProximityPrize.Benchmark RCN095 RCN275 RCN198 RCN206 RCN263
open scoped NNReal
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def score:ℕ:=6738
def errors:ℕ:=80150
def agreements:ℕ:=n - errors
def gap:ℕ:=agreements - w
def radiusNumerator:ℕ:=10259200
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
structure Profile where
 multiplicity:ℕ
 totalCap:ℕ
 slopeCap:ℕ
 middleCap:ℕ
 deriving DecidableEq
namespace Profile
def weightedCap (P:Profile):ℕ:=P.multiplicity * agreements
end Profile
def profileA:Profile:=⟨44,84442,13,61⟩
def profileB:Profile:=⟨81,1379,25,112⟩
def profileC:Profile:=⟨43,41790,13,59⟩
def profileH:Profile:=⟨42,1261,12,55⟩
def supportYS:ResidualSupportParameters :=
 RCN198.support 1207 41 10
def supportS:ResidualSupportParameters :=
 RCN198.support 1206 43 9
def fixedFlagYS:FlagDegree:=surfaceFlag 1207 41 10
def fixedFlagS:FlagDegree:=surfaceFlag 1206 43 9
def firstTailYS:FlagDegree:=reducedResidualAgreementFlag supportYS (w + 1)
def secondTailYS:FlagDegree:=reducedResidualAgreementFlag supportYS (w + 2)
def firstTailS:FlagDegree:=reducedResidualAgreementFlag supportS (w + 1)
def secondTailS:FlagDegree:=reducedResidualAgreementFlag supportS (w + 2)
def fixedRegularCostYS:ℕ:=flagMixed fixedFlagYS firstTailYS secondTailYS
def fixedSingularCostYS:ℕ:=76778677599070
def firstResidualRegularCostYS:ℕ:=9644144290222
def firstResidualSingularCostYS:ℕ:=235470664
def secondResidualRegularCostYS:ℕ:=0
def secondResidualSingularCostYS:ℕ:=4646124
def fixedRegularCostS:ℕ:=flagMixed fixedFlagS firstTailS secondTailS
def fixedSingularCostS:ℕ:=63997115995699
def firstResidualRegularCostS:ℕ:=15868064433192
def firstResidualSingularCostS:ℕ:=235470664
def secondResidualRegularCostS:ℕ:=2376733763872
def secondResidualSingularCostS:ℕ:=4646124
def fixedCostYS:ℕ:=fixedRegularCostYS + fixedSingularCostYS
def firstResidualCeilingYS:ℕ :=
 firstResidualRegularCostYS + firstResidualSingularCostYS
def secondResidualCeilingYS:ℕ :=
 secondResidualRegularCostYS + secondResidualSingularCostYS
def totalCostYS:ℕ :=
 fixedCostYS + firstResidualCeilingYS + secondResidualCeilingYS
def fixedCostS:ℕ:=fixedRegularCostS + fixedSingularCostS
def firstResidualCeilingS:ℕ :=
 firstResidualRegularCostS + firstResidualSingularCostS
def secondResidualCeilingS:ℕ :=
 secondResidualRegularCostS + secondResidualSingularCostS
def totalCostS:ℕ :=
 fixedCostS + firstResidualCeilingS + secondResidualCeilingS
def capacity:ℕ:=prime ^ 6 / 2 ^ 128
def listBudget:ℕ:=1000000000
def mcaBudget:ℕ:=capacity - listBudget
theorem basic_values :
   agreements = 181994 ∧ gap = 50923 ∧
     profileA.weightedCap = 8007736 ∧
     profileB.weightedCap = 14741514 ∧
     profileC.weightedCap = 7825742:=by
 decide
theorem support_values :
   supportYS.s = 12 ∧ supportYS.ys = 54 ∧ supportYS.total = 1261 ∧
     supportS.s = 11 ∧ supportS.ys = 55 ∧ supportS.total = 1261:=by
 decide
theorem fixed_flag_values :
   fixedFlagYS = ⟨1207,42,12⟩ ∧
     fixedFlagS = ⟨1206,44,11⟩:=by
 decide
theorem exact_costs :
   fixedRegularCostYS = 274157428415717762 ∧
     totalCostYS = 274243851477723842 ∧
     fixedRegularCostS = 257774510141394427 ∧
     totalCostS = 257856752295703978:=by
 decide
theorem budget_values :
   capacity = 274980728111395087 ∧
     mcaBudget = 274980727111395087 ∧
     totalCostYS < mcaBudget ∧ totalCostS < mcaBudget:=by
 decide
theorem radius_floor :
   ⌊(radius:ℝ) * (Fintype.card IRSProfile.Index:ℝ)⌋₊ = errors:=by
 norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
   errors, IRSProfile.Index]
theorem radius_admissible :
   radius ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance:=by
 constructor <;>
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator,
     IRSProfile.minRelativeDistance]
theorem score_root_integer:(2:ℕ) ^ 38 * 521 ^ 100 ≤ 678 ^ 100:=by
 decide
theorem score_radius_integer :
   (23295232:ℕ) ^ 128 * (2 ^ 67 * 678) ≤ 521 * 33554432 ^ 128:=by
 decide
theorem two_rpow_score_fraction_le :
   (2:ℝ≥0) ^ ((38:ℝ) / 100) ≤ (678:ℝ≥0) / 521:=by
 have hroot:((2:ℝ≥0) ^ (38:ℕ)) ^ ((100:ℝ)⁻¹) ≤
     (678:ℝ≥0) / 521:=by
   rw [NNReal.rpow_inv_le_iff (by norm_num:(0:ℝ) < 100)]
   rw [NNReal.rpow_ofNat, div_pow, le_div_iff₀ (by positivity)]
   exact_mod_cast score_root_integer
 calc
   (2:ℝ≥0) ^ ((38:ℝ) / 100) =
       ((2:ℝ≥0) ^ (38:ℕ)) ^ ((100:ℝ)⁻¹):=by
     rw [← NNReal.rpow_natCast_mul]
     norm_num [div_eq_mul_inv]
   _ ≤ (678:ℝ≥0) / 521:=hroot
theorem radius_power_rational_bound :
   (1 - radius) ^ IRSProfile.repetitions ≤
     ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (521 / 678):=by
 have hsub:(1 - radius:ℝ≥0) = 23295232 / 33554432:=by
   have hr:radius ≤ 1:=by
     rw [← NNReal.coe_le_coe]
     norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
   apply NNReal.coe_injective
   rw [NNReal.coe_sub hr]
   norm_num [radius, claimedRadius, radiusNumerator, radiusDenominator]
 change (1 - radius) ^ 128 ≤ ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (521 / 678)
 rw [hsub, div_pow, div_mul_div_comm, one_mul,
   div_le_div_iff₀ (by positivity) (by positivity)]
 exact_mod_cast score_radius_integer
theorem score_target_le :
   (1 - radius) ^ IRSProfile.repetitions ≤ claimedError score:=by
 have hscale:(521:ℝ≥0) / 678 ≤
     (2:ℝ≥0) ^ (-((38:ℝ) / 100)):=by
   calc
     (521:ℝ≥0) / 678 = 1 / ((678:ℝ≥0) / 521):=by norm_num
     _ ≤ 1 / ((2:ℝ≥0) ^ ((38:ℝ) / 100)) :=
       one_div_le_one_div_of_le (by positivity) two_rpow_score_fraction_le
     _ = (2:ℝ≥0) ^ (-((38:ℝ) / 100)):=by
       rw [one_div, NNReal.rpow_neg]
 calc
   (1 - radius) ^ IRSProfile.repetitions ≤
       ((1:ℝ≥0) / 2 ^ (67:ℕ)) * (521 / 678) :=
     radius_power_rational_bound
   _ ≤ ((1:ℝ≥0) / 2 ^ (67:ℕ)) *
       (2:ℝ≥0) ^ (-((38:ℝ) / 100)) :=
     mul_le_mul_of_nonneg_left hscale (by positivity)
   _ = claimedError score:=by
     unfold claimedError score
     rw [show -((((6738:ℕ):ℝ) / 100)) =
         -((67:ℕ):ℝ) + -((38:ℝ) / 100) by norm_num,
       NNReal.rpow_add (by norm_num:(2:ℝ≥0) ≠ 0)]
     simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]
end
end ProximityPrize.SubmissionLower.RCN327
