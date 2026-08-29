import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

/-! .
 -/
namespace ProximityPrize.SubmissionLower.ContactMovingParameters6719Research

open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactFlagBezout6543Research
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def errors : ℕ := 79964
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def listBudget : ℕ := 700000000
def capacity : ℕ := prime ^ 6 / 2 ^ 128
def mcaBudget : ℕ := capacity - listBudget

structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq

def profileA : Profile := ⟨37, 52037, 10⟩
def profileB : Profile := ⟨71, 1019, 22⟩
def profileC : Profile := profileB
def profileMeet : Profile := ⟨37, 1019, 10⟩

namespace Profile
def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
def yCap (P : Profile) : ℕ := (P.weightedCap - 1) / w
def coefficients (P : Profile) : ℕ :=
  coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P : Profile) : ℕ :=
  localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P : Profile) : ℕ := n * P.localRank
def nullity (P : Profile) : ℕ := P.coefficients - P.totalRank
def characteristicCap (P : Profile) : ℕ :=
  (2 * P.slopeCap - 1) * P.weightedCap
end Profile

theorem base_values : agreements = 182180 ∧ gap = 51109 ∧
    capacity = 274980728111395087 ∧ mcaBudget = 274980727411395087 ∧
    mcaBudget + listBudget = capacity := by decide

theorem profileA_coefficients_exact : profileA.coefficients = 82955861521313 := by
  change coefficientCount (37 * 182180) 131071 52037 10 = 82955861521313
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (37 * 182180) 131071 52037 10 52 (by decide) (by decide)]
  decide

theorem profileA_localRank_exact : profileA.localRank = 316451498 := by
  change localRankBound 37 52037 10 = 316451498
  decide

theorem profileB_coefficients_exact : profileB.coefficients = 11561410213210 := by
  change coefficientCount (71 * 182180) 131071 1019 22 = 11561410213210
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (71 * 182180) 131071 1019 22 99 (by decide) (by decide)]
  decide

theorem profileB_localRank_exact : profileB.localRank = 44103236 := by
  change localRankBound 71 1019 22 = 44103236
  decide

theorem profile_values :
    profileA.weightedCap = 6740660 ∧ profileB.weightedCap = 12934780 ∧
    profileA.yCap = 51 ∧ profileB.yCap = 98 ∧
    profileA.nullity = 29601 ∧ profileB.nullity = 11515226 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩
  · rw [Profile.nullity, Profile.totalRank,
      profileA_coefficients_exact, profileA_localRank_exact]
    decide
  · rw [Profile.nullity, Profile.totalRank,
      profileB_coefficients_exact, profileB_localRank_exact]
    decide

theorem interpolation_gates :
    profileA.totalRank < profileA.coefficients ∧
    profileB.totalRank < profileB.coefficients ∧
    profileC.totalRank < profileC.coefficients := by
  simp only [profileC, Profile.totalRank]
  rw [profileA_coefficients_exact, profileA_localRank_exact,
    profileB_coefficients_exact, profileB_localRank_exact]
  decide

theorem characteristic_gates :
    profileA.characteristicCap < prime ∧
    (2 * profileA.slopeCap - 1) * profileA.seedCap < prime ∧
    profileA.slopeCap < prime ∧
    profileB.characteristicCap < prime ∧
    (2 * profileB.slopeCap - 1) * profileB.seedCap < prime ∧
    profileB.slopeCap < prime := by decide

theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity,
      min profileA.seedCap profileB.seedCap, min profileA.slopeCap profileB.slopeCap) =
        (profileMeet.multiplicity, profileMeet.seedCap, profileMeet.slopeCap) ∧
    (min profileMeet.multiplicity profileC.multiplicity,
      min profileMeet.seedCap profileC.seedCap, min profileMeet.slopeCap profileC.slopeCap) =
        (37, 1019, 10) := by decide

theorem middle_support_gates :
    profileA.weightedCap + profileA.slopeCap ≤ w * (profileA.yCap + 1) ∧
    profileB.weightedCap + profileB.slopeCap ≤ w * (profileB.yCap + 1) ∧
    profileA.multiplicity - 1 + profileA.slopeCap ≤ profileA.yCap ∧
    profileB.multiplicity - 1 + profileB.slopeCap ≤ profileB.yCap := by decide

def fixedFlag : FlagDegree := ⟨968, 41, 10⟩
def direction : FlagDegree := ⟨1936, 82, 18⟩
def normal : FlagDegree := ⟨968, 40, 8⟩
def fiber : FlagDegree := ⟨968, 41, 11⟩
def surface : FlagDegree := fixedFlag
def centre : FlagDegree := ⟨1936, 82, 19⟩
def degreeSlope : ℕ :=
  flagMixed fixedFlag direction normal + flagMixed fixedFlag fiber surface
def degreeBase : ℕ :=
  flagMixed fixedFlag unitYZFlag normal + flagMixed fixedFlag fiber centre
def unitSlope : ℕ := flagMixed fixedFlag direction centre
def unitBase : ℕ := flagMixed fixedFlag unitYZFlag centre
def zSlope : ℕ := flagMixed fixedFlag direction unitZFlag
def yzSlope : ℕ := flagMixed fixedFlag direction unitYZFlag
def zBase : ℕ := flagMixed fixedFlag unitYZFlag unitZFlag
def yzBase : ℕ := flagMixed fixedFlag unitYZFlag unitYZFlag
def qeff : ℕ := degreeSlope
def E : ℕ := (n * gap * w + agreements - 1) / agreements
def U : ℕ := n - w

def primary : ℕ := degreeSlope * E ^ 2 +
  (degreeBase + unitSlope) * E * U + unitBase * U ^ 2
def zTail : ℕ := (errors + 1) * gap * (zSlope * E + zBase * U)
def yzTail : ℕ := (errors + 1) * gap * (yzSlope * E + yzBase * U)
def fixedRegularCost : ℕ := (primary + zTail + yzTail) / gap ^ 2 + 1

theorem flag_values : qeff = 7665099 ∧ degreeBase = 5589370 ∧
    unitSlope = 10335656 ∧ unitBase = 39541 ∧ U = 131073 := by decide

def singularY (P : Profile) : ℕ := (P.characteristicCap - 1) / w
def singularZ (P : Profile) : ℕ := (2 * P.slopeCap - 1) * P.seedCap
def singularNumerator (P : Profile) : ℕ :=
  let y := singularY P
  let z := singularZ P
  U * ((1 + 2*w*y)*z + w*(2*y*z) + (2*w*z + 1)*y) +
    (errors + 1)*gap*y + 2*z*z*gap
def singularCeiling (P : Profile) : ℕ := singularNumerator P / gap + 1

def residualMixed (P Q : Profile) : Fin 3 → ℕ :=
  ![P.slopeCap*Q.seedCap + P.seedCap*Q.slopeCap,
    P.yCap*Q.seedCap + P.seedCap*Q.yCap,
    P.yCap*Q.slopeCap + P.slopeCap*Q.yCap]
def residualNumerator (P Q : Profile) : ℕ :=
  let c := residualMixed P Q
  U * (c 0*(1 + 2*w*max P.yCap Q.yCap) +
    c 1*(w*(2*max P.slopeCap Q.slopeCap - 1)) +
    c 2*(2*w*max P.seedCap Q.seedCap + 1)) + (errors + 1)*gap*c 2

def fixedSingularCost : ℕ := singularCeiling profileMeet
def firstResidualRegularCost : ℕ := residualNumerator profileA profileB / gap
def firstResidualSingularCeiling : ℕ := singularCeiling profileB
def secondResidualRegularCost : ℕ := residualNumerator profileMeet profileC / gap
def secondResidualSingularCeiling : ℕ := singularCeiling profileMeet
def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ := firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ := secondResidualRegularCost + secondResidualSingularCeiling
def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem padded_incidence_values :
    E = 9639249481 ∧ zSlope = 1738 ∧ yzSlope = 38522 ∧
    zBase = 10 ∧ yzBase = 10 ∧
    primary = 712223794717697532745437666 ∧
    zTail = 68468427247031023258980 ∧
    yzTail = 1517572242441466631267220 ∧
    primary + zTail + yzTail = 713809835387386030399963866 := by decide

theorem residual_numerators_exact :
    residualNumerator profileA profileB = 11453190445611892419 ∧
    residualNumerator profileMeet profileC = 295567233592398891 := by decide

theorem six_cells_exact :
    fixedRegularCost = 273267359551860672 ∧
    fixedSingularCost = 38150961897803 ∧
    firstResidualRegularCost = 224093416924844 ∧
    firstResidualSingularCeiling = 374968021454319 ∧
    secondResidualRegularCost = 5783076045166 ∧
    secondResidualSingularCeiling = 38150961897803 := by decide

theorem total_and_slack_exact :
    totalCost = 273948505990080607 ∧
    mcaBudget - totalCost = 1032221421314480 ∧ totalCost < mcaBudget := by decide

theorem residual_characteristic_gates :
    residualMixed profileA profileB = ![1155004, 5151595, 2102] ∧
    residualMixed profileMeet profileC = ![32608, 151831, 2102] ∧
    profileB.characteristicCap = 556195540 ∧ singularZ profileB = 43817 ∧
    singularY profileB = 4243 ∧ 2*singularY profileB*singularZ profileB < prime ∧
    profileMeet.characteristicCap = 128072540 ∧ singularZ profileMeet = 19361 ∧
    singularY profileMeet = 977 ∧ 2*singularY profileMeet*singularZ profileMeet < prime ∧
    (1 + w*(direction.yz + direction.all))*fixedFlag.all +
      (fixedFlag.yz + fixedFlag.all)*(w*direction.all) < prime := by decide

/-- . -/
theorem total_lt_mcaBudget (total firstResidual secondResidual fixed : ℕ)
    (hpartition : total = firstResidual + secondResidual + fixed)
    (hfirst : firstResidual < firstResidualCeiling)
    (hsecond : secondResidual < secondResidualCeiling) (hfixed : fixed ≤ fixedCost) :
    total < mcaBudget := by
  have hsum : firstResidual + secondResidual + fixed < totalCost := by
    unfold totalCost
    omega
  rw [hpartition]
  exact hsum.trans total_and_slack_exact.2.2

end ProximityPrize.SubmissionLower.ContactMovingParameters6719Research
