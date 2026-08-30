import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactFlagRankKernel6641Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
open ProximityPrize.Benchmark
open ContactFlagBezout6543Research
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open scoped NNReal
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
def n:ℕ:=262144
def w:ℕ:=131071
def prime:ℕ:=2130706433
def score:ℕ:=6734
def errors:ℕ:=80102
def agreements:ℕ:=n-errors
def gap:ℕ:=agreements-w
def radiusNumerator:ℕ:=128*errors+127
def radiusDenominator:ℕ:=33554432
def radius:ℝ≥0:=claimedRadius radiusNumerator radiusDenominator
structure Profile where
  multiplicity:ℕ
  totalCap:ℕ
  slopeCap:ℕ
  middleCap:ℕ
  coefficients:ℕ
  rank:ℕ
  deriving DecidableEq
namespace Profile
def nullity (P:Profile):ℕ:=P.coefficients-n*P.rank
def weightedCap (P:Profile):ℕ:=P.multiplicity*agreements
def yCap (P:Profile):ℕ:=(P.weightedCap-1)/w
def totalRank (P:Profile):ℕ:=n*P.rank
def characteristicCap (P:Profile):ℕ:=
  (2*P.slopeCap-1)*P.weightedCap
end Profile
def profileA:Profile:=⟨43,8000,12,59,20077376487545,76584352⟩
def profileB:Profile:=⟨81,1262,25,112,21082509737588,80423213⟩
def profileC:Profile:=⟨43,8000,12,59,20077376487545,76584352⟩
def finalMeet:Profile:=⟨43,1262,12,59,0,0⟩
def fixedFlag:FlagDegree:=
  ⟨finalMeet.totalCap-finalMeet.middleCap,
    finalMeet.middleCap-finalMeet.slopeCap,
    finalMeet.slopeCap⟩
def direction:FlagDegree:=
  ⟨2*fixedFlag.zOnly,2*fixedFlag.yz-1,2*fixedFlag.all-1⟩
def tailFlag (d:ℕ):FlagDegree:=unitYZFlag+(d+1) • direction
def fixedRegularCost:ℕ:=flagMixed fixedFlag (tailFlag (w+1)) (tailFlag (w+2))
def fixedSingularCost:ℕ:=80596345495370
def firstResidualRegularCost:ℕ:=47473538768802
def firstResidualSingularCost:ℕ:=689314936957386
def secondResidualRegularCost:ℕ:=16293039752618
def secondResidualSingularCost:ℕ:=80596345495370
def fixedCost:ℕ:=fixedRegularCost+fixedSingularCost
def firstResidualCeiling:ℕ:=
  firstResidualRegularCost+firstResidualSingularCost
def secondResidualCeiling:ℕ:=
  secondResidualRegularCost+secondResidualSingularCost
def totalCost:ℕ:=
  fixedRegularCost+fixedSingularCost+
    firstResidualRegularCost+firstResidualSingularCost+
    secondResidualRegularCost+secondResidualSingularCost
def seedlessListNumerator:ℕ:=46024937937114
def seedlessListCeiling:ℕ:=seedlessListNumerator/gap+1
def capacity:ℕ:=prime^6/2^128
def mcaBudget:ℕ:=capacity-seedlessListCeiling
def slack:ℕ:=mcaBudget-totalCost
abbrev scoreGate (e:ℕ):Prop:=
  (radiusDenominator-(128*e+127))^12800*2^score ≤
    radiusDenominator^12800
theorem radius_row_exact:
    errors=80102∧agreements=182042∧gap=50971∧
      radiusNumerator=10253183∧radiusDenominator=33554432:=by
  decide
theorem radius_cell_exact:scoreGate errors∧¬ scoreGate (errors-1):=by
  decide
theorem profile_values:
    profileA.nullity=1248116857∧profileB.nullity=46988916∧
      profileC.nullity=1248116857∧
      finalMeet=⟨43,1262,12,59,0,0⟩:=by
  decide
theorem profileA_coefficients_exact:
    coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap=
      profileA.coefficients:=by
  change coefficientCount (43*182042) 131071 8000 12=20077376487545
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (43*182042) 131071 8000 12 60 (by decide) (by decide)]
  decide
theorem profileB_coefficients_exact:
    coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap=
      profileB.coefficients:=by
  change coefficientCount (81*182042) 131071 1262 25=21082509737588
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (81*182042) 131071 1262 25 113 (by decide) (by decide)]
  decide
theorem profileC_coefficients_exact:
    coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap=
      profileC.coefficients:=by
  change coefficientCount (43*182042) 131071 8000 12=20077376487545
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (43*182042) 131071 8000 12 60 (by decide) (by decide)]
  decide
theorem profileA_rank_exact:
    localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap=
      profileA.rank:=by decide
theorem profileB_rank_exact:
    localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap=
      profileB.rank:=by decide
theorem profileC_rank_exact:
    localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap=
      profileC.rank:=by decide
theorem interpolation_gates:
    profileA.totalRank < profileA.coefficients∧
      profileB.totalRank < profileB.coefficients∧
      profileC.totalRank < profileC.coefficients:=by
  decide
theorem interpolation_gateA_exact:
    n*localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap <
      coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap:=by
  rw [profileA_coefficients_exact,profileA_rank_exact]
  decide
theorem interpolation_gateB_exact:
    n*localRankBound profileB.multiplicity profileB.totalCap profileB.slopeCap <
      coefficientCount profileB.weightedCap w profileB.totalCap profileB.slopeCap:=by
  rw [profileB_coefficients_exact,profileB_rank_exact]
  decide
theorem interpolation_gateC_exact:
    n*localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap <
      coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap:=by
  rw [profileC_coefficients_exact,profileC_rank_exact]
  decide
theorem profile_gates:
    profileA.characteristicCap < prime∧
      profileB.characteristicCap < prime∧
      profileC.characteristicCap < prime∧
      profileA.weightedCap+profileA.slopeCap ≤ w*(profileA.yCap+1)∧
      profileB.weightedCap+profileB.slopeCap ≤ w*(profileB.yCap+1)∧
      profileC.weightedCap+profileC.slopeCap ≤ w*(profileC.yCap+1)∧
      profileA.multiplicity-1+profileA.slopeCap ≤ profileA.yCap∧
      profileB.multiplicity-1+profileB.slopeCap ≤ profileB.yCap∧
      profileC.multiplicity-1+profileC.slopeCap ≤ profileC.yCap:=by
  decide
theorem profile_small_gates:
    (2*profileA.slopeCap-1)*profileA.totalCap < prime∧
      profileA.slopeCap < prime∧
      (2*profileB.slopeCap-1)*profileB.totalCap < prime∧
      profileB.slopeCap < prime∧
      (2*profileC.slopeCap-1)*profileC.totalCap < prime∧
      profileC.slopeCap < prime:=by
  decide
theorem fixed_flag_values:
    fixedFlag=⟨1203,47,12⟩∧direction=⟨2406,93,23⟩∧
      tailFlag (w+1)=⟨315361638,12189790,3014679⟩∧
      tailFlag (w+2)=⟨315364044,12189883,3014702⟩:=by
  decide
theorem six_cells_exact:
    fixedRegularCost=270046217001125523∧
      fixedSingularCost=80596345495370∧
      firstResidualRegularCost=47473538768802∧
      firstResidualSingularCost=689314936957386∧
      secondResidualRegularCost=16293039752618∧
      secondResidualSingularCost=80596345495370:=by
  decide
theorem budget_and_slack_exact:
    seedlessListCeiling=902963214∧
      capacity=274980728111395087∧
      totalCost=270960491207595069∧
      mcaBudget=274980727208431873∧
      slack=4020236000836804∧totalCost < mcaBudget:=by
  decide
theorem cell_budget_strict:
    fixedCost+firstResidualCeiling+secondResidualCeiling < mcaBudget:=by
  decide
end
end ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
