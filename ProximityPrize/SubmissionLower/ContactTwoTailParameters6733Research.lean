import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactFlagRankKernel6641Research
import ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch
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
def score:ℕ:=6767
def errors:ℕ:=80427
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
def profileA:Profile:=⟨64,400000,20,88,3475529838735717,13243089090⟩
def profileB:Profile:=⟨130,1000,38,180,67178696741,254774⟩
def profileC:Profile:=⟨71,1600000,18,98,16173386552979645,61650084510⟩
def finalMeet:Profile:=⟨64,1000,18,88,0,0⟩
def fixedFlag:FlagDegree:=
  ⟨0,
    finalMeet.middleCap-finalMeet.slopeCap,
    finalMeet.slopeCap⟩
def direction:FlagDegree:=
  ⟨2*fixedFlag.zOnly,2*fixedFlag.yz-1,2*fixedFlag.all-1⟩
def tailFlag (d:ℕ):FlagDegree:=unitYZFlag+(d+1) • direction
def fixedRegularCost:ℕ:=flagMixed fixedFlag (tailFlag (w+1)) (tailFlag (w+2))
def fixedSingularCost:ℕ:=220545077254377
def firstResidualRegularCost:ℕ:=5577029963253399
def firstResidualSingularCost:ℕ:=2063336810895960
def secondResidualRegularCost:ℕ:=7839710703227545
def secondResidualSingularCost:ℕ:=274645133867136
def fixedCost:ℕ:=fixedRegularCost+fixedSingularCost
def firstResidualCeiling:ℕ:=
  firstResidualRegularCost+firstResidualSingularCost
def secondResidualCeiling:ℕ:=
  secondResidualRegularCost+secondResidualSingularCost
def totalCost:ℕ:=
  fixedRegularCost+fixedSingularCost+
    firstResidualRegularCost+firstResidualSingularCost+
    secondResidualRegularCost+secondResidualSingularCost
def seedlessListNumerator:ℕ:=86586668381568
def seedlessListCeiling:ℕ:=seedlessListNumerator/gap+1
def capacity:ℕ:=prime^6/2^128
def mcaBudget:ℕ:=capacity-seedlessListCeiling
def slack:ℕ:=mcaBudget-totalCost
abbrev scoreGate (e:ℕ):Prop:=
  (radiusDenominator-(128*e+127))^12800*2^score ≤
    radiusDenominator^12800
abbrev scoreGatePlus (e:ℕ):Prop:=
  (radiusDenominator-(128*e+127))^12800*2^(score+1) ≤
    radiusDenominator^12800
theorem radius_row_exact:
    errors=80427∧agreements=181717∧gap=50646∧
      radiusNumerator=10294783∧radiusDenominator=33554432:=by
  decide
theorem radius_cell_exact:scoreGate errors∧¬ scoreGatePlus errors:=by
  decide
theorem profile_values:
    profileA.nullity=3933492326757∧profileB.nullity=391221285∧
      profileC.nullity=12186799190205∧
      finalMeet=⟨64,1000,18,88,0,0⟩:=by
  decide
theorem profileA_coefficients_exact:
      coefficientCount profileA.weightedCap w profileA.totalCap profileA.slopeCap=
        profileA.coefficients:=by
  change coefficientCount (64*181717) 131071 400000 20=3475529838735717
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (64*181717) 131071 400000 20 89 (by decide) (by decide)]
  decide
theorem profileB_coefficients_exact:
      ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch.coefficientCount
        profileB.weightedCap w profileB.totalCap profileB.slopeCap=
      profileB.coefficients:=by
  change ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch.coefficientCount
    (130*181717) 131071 1000 38=67178696741
  native_decide
theorem profileC_coefficients_exact:
      coefficientCount profileC.weightedCap w profileC.totalCap profileC.slopeCap=
        profileC.coefficients:=by
  change coefficientCount (71*181717) 131071 1600000 18=16173386552979645
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (71*181717) 131071 1600000 18 99 (by decide) (by decide)]
  decide
theorem profileA_rank_exact:
    localRankBound profileA.multiplicity profileA.totalCap profileA.slopeCap=
      profileA.rank:=by native_decide
theorem profileB_rank_exact:
    ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch.localRankBound
      profileB.multiplicity profileB.totalCap profileB.slopeCap=
      profileB.rank:=by native_decide
theorem profileC_rank_exact:
    localRankBound profileC.multiplicity profileC.totalCap profileC.slopeCap=
      profileC.rank:=by native_decide
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
    n*ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch.localRankBound
      profileB.multiplicity profileB.totalCap profileB.slopeCap <
      ProximityPrize.SubmissionLower.ContactSeedlessInterpolationResearch.coefficientCount
        profileB.weightedCap w profileB.totalCap profileB.slopeCap:=by
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
      profileC.multiplicity-1+profileC.slopeCap ≤ profileC.yCap∧
      (2*profileA.slopeCap-1)*profileA.totalCap < prime∧
      profileA.slopeCap < prime∧
      (2*profileB.slopeCap-1)*profileB.totalCap < prime∧
      profileB.slopeCap < prime∧
      (2*profileC.slopeCap-1)*profileC.totalCap < prime∧
      profileC.slopeCap < prime:=by
  decide
theorem fixed_flag_values:
    fixedFlag=⟨0,70,18⟩∧direction=⟨0,139,35⟩∧
      tailFlag (w+1)=⟨0,18219148,4587555⟩∧
      tailFlag (w+2)=⟨0,18219287,4587590⟩:=by
  decide
theorem six_cells_exact:
    fixedRegularCost=22537378926971408∧
      fixedSingularCost=220545077254377∧
      firstResidualRegularCost=5577029963253399∧
      firstResidualSingularCost=2063336810895960∧
      secondResidualRegularCost=7839710703227545∧
      secondResidualSingularCost=274645133867136:=by
  decide
theorem budget_and_slack_exact:
    seedlessListCeiling=1709644758∧
      capacity=274980728111395087∧
      totalCost=38512646615469825∧
      mcaBudget=274980726401750329∧
      slack=236468079786280504∧totalCost < mcaBudget:=by
  decide
theorem cell_budget_strict:
    fixedCost+firstResidualCeiling+secondResidualCeiling < mcaBudget:=by
  decide
end
end ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
