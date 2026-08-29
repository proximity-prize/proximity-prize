import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactStackedParameters6670Research
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger6719Research
import ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger6720Research

/-! Exact arithmetic for the conditional 67.32+ reduced-first-tail row at 80,084 errors. -/
namespace ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
open ContactFlagInterpolation6641Research ContactFlagRankKernel6641Research
open ContactFlagBezout6543Research ContactMovingPositiveLedger6719Research
open ContactResidualSupportParametersResearch
open ContactMovingReducedPositiveLedger6720Research
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def errors : ℕ := 80084
def agreements : ℕ := n - errors
def gap : ℕ := agreements - w
def listBudget : ℕ := 1000000000
def capacity : ℕ := prime^6 / 2^128
def mcaBudget : ℕ := capacity - listBudget

structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq
def profileA : Profile := ⟨43, 48000, 11⟩
def profileB : Profile := ⟨81, 1225, 25⟩
def profileC : Profile := ⟨40, 91386, 12⟩
def profileABMeet : Profile := ⟨43, 1225, 11⟩
def profileFinalMeet : Profile := ⟨40, 1225, 11⟩
namespace Profile
def weightedCap (P : Profile) : ℕ := P.multiplicity * agreements
def yCap (P : Profile) : ℕ := (P.weightedCap - 1) / w
def coefficients (P : Profile) : ℕ := coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P : Profile) : ℕ := localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P : Profile) : ℕ := n * P.localRank
def nullity (P : Profile) : ℕ := P.coefficients - P.totalRank
def characteristicCap (P : Profile) : ℕ := (2 * P.slopeCap - 1) * P.weightedCap
end Profile

theorem base_values : agreements = 182060 ∧ gap = 50989 ∧
    capacity = 274980728111395087 ∧ mcaBudget = 274980727111395087 ∧
    mcaBudget + listBudget = capacity := by decide

theorem profileA_coefficients_exact : profileA.coefficients = 113454345492476 := by
  change coefficientCount (43 * 182060) 131071 48000 11 = 113454345492476
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (43 * 182060) 131071 48000 11 60 (by decide) (by decide)]
  decide

theorem profileB_coefficients_exact : profileB.coefficients = 20456108157792 := by
  change coefficientCount (81 * 182060) 131071 1225 25 = 20456108157792
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (81 * 182060) 131071 1225 25 113 (by decide) (by decide)]
  decide

theorem profileC_coefficients_exact : profileC.coefficients = 196163351989529 := by
  change coefficientCount (40 * 182060) 131071 91386 12 = 196163351989529
  rw [ContactStackedParameters6670Research.coefficientCount_eq_sum_range_of_weighted_cutoff
    (40 * 182060) 131071 91386 12 56 (by decide) (by decide)]
  decide

theorem profileA_rank_exact : profileA.localRank = 432792704 := by decide
theorem profileB_rank_exact : profileB.localRank = 78033285 := by decide
theorem profileC_rank_exact : profileC.localRank = 748316114 := by decide

theorem profile_values :
    profileA.weightedCap = 7828580 ∧ profileB.weightedCap = 14746860 ∧
    profileC.weightedCap = 7282400 ∧ profileA.yCap = 59 ∧ profileB.yCap = 112 ∧
    profileC.yCap = 55 ∧ profileABMeet.yCap = 59 ∧ profileFinalMeet.yCap = 55 ∧
    profileA.nullity = 124652533 ∧ profileB.nullity = 169215488 ∧ profileC.nullity = 66313 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [Profile.nullity, Profile.totalRank, profileA_coefficients_exact, profileA_rank_exact]; decide
  · rw [Profile.nullity, Profile.totalRank, profileB_coefficients_exact, profileB_rank_exact]; decide
  · rw [Profile.nullity, Profile.totalRank, profileC_coefficients_exact, profileC_rank_exact]; decide

theorem interpolation_gates : profileA.totalRank < profileA.coefficients ∧
    profileB.totalRank < profileB.coefficients ∧ profileC.totalRank < profileC.coefficients := by
  change n * profileA.localRank < profileA.coefficients ∧ n * profileB.localRank < profileB.coefficients ∧
    n * profileC.localRank < profileC.coefficients
  rw [profileA_coefficients_exact, profileA_rank_exact,
    profileB_coefficients_exact, profileB_rank_exact, profileC_coefficients_exact, profileC_rank_exact]
  decide

theorem meet_caps :
    (min profileA.multiplicity profileB.multiplicity, min profileA.seedCap profileB.seedCap,
      min profileA.slopeCap profileB.slopeCap) =
      (profileABMeet.multiplicity, profileABMeet.seedCap, profileABMeet.slopeCap) ∧
    (min profileABMeet.multiplicity profileC.multiplicity,
      min profileABMeet.seedCap profileC.seedCap, min profileABMeet.slopeCap profileC.slopeCap) =
      (profileFinalMeet.multiplicity, profileFinalMeet.seedCap, profileFinalMeet.slopeCap) := by decide

theorem profile_gates :
    profileA.characteristicCap < prime ∧ profileB.characteristicCap < prime ∧
    profileC.characteristicCap < prime ∧
    profileA.weightedCap + profileA.slopeCap ≤ w * (profileA.yCap + 1) ∧
    profileB.weightedCap + profileB.slopeCap ≤ w * (profileB.yCap + 1) ∧
    profileC.weightedCap + profileC.slopeCap ≤ w * (profileC.yCap + 1) ∧
    profileA.multiplicity - 1 + profileA.slopeCap ≤ profileA.yCap ∧
    profileB.multiplicity - 1 + profileB.slopeCap ≤ profileB.yCap ∧
    profileC.multiplicity - 1 + profileC.slopeCap ≤ profileC.yCap := by decide

theorem profile_small_gates :
    (2 * profileA.slopeCap - 1) * profileA.seedCap < prime ∧ profileA.slopeCap < prime ∧
    (2 * profileB.slopeCap - 1) * profileB.seedCap < prime ∧ profileB.slopeCap < prime ∧
    (2 * profileC.slopeCap - 1) * profileC.seedCap < prime ∧ profileC.slopeCap < prime := by decide

def fixedSupport : ResidualSupportParameters :=
  ContactMovingAgreementCertificate6719Research.support 1169 43 9

def fixedProfileForLedger : ContactRobustFixedMeet6656Research.Profile :=
  ⟨262144, 131071, 182060, 7282400, 1225, 11⟩

def fixedFlag : FlagDegree := surfaceFlag 1169 43 9
def direction : FlagDegree := directionFlag 1169 43 9
def centre : FlagDegree := centreFlag 1169 43 9
def E : ℕ := (n * gap * w + agreements - 1) / agreements
def U : ℕ := n - w

def degreeCost : ℕ :=
  ContactMovingReducedFactorLedger6720Research.factorDegreeCost
    fixedProfileForLedger fixedSupport 1169 43 9 fixedFlag

def unitCost : ℕ :=
  ContactMovingReducedFactorLedger6720Research.factorUnitCost
    fixedProfileForLedger fixedSupport 1169 43 9 fixedFlag

def fixedProperTailCost : ℕ := ((w + 1) * degreeCost + unitCost) / gap + 1

def identityFlag : FlagDegree := centre + (w + 1) • direction
def firstTailFlag : FlagDegree := centre + w • direction
def identityZDegree : ℕ := flagMixed fixedFlag identityFlag unitZFlag
def identityYZDegree : ℕ := flagMixed fixedFlag identityFlag unitYZFlag
def fixedIdentityYZCost : ℕ := U * (errors + 1) * (identityZDegree + identityYZDegree) / gap + 1
def fixedRegularCost : ℕ := fixedProperTailCost + fixedIdentityYZCost

def singularY (P : Profile) : ℕ := (P.characteristicCap - 1) / w
def singularZ (P : Profile) : ℕ := (2 * P.slopeCap - 1) * P.seedCap
def singularNumerator (P : Profile) : ℕ :=
  let y := singularY P; let z := singularZ P
  U * ((1 + 2 * w * y) * z + w * (2 * y * z) + (2 * w * z + 1) * y) + (errors + 1) * gap * y + 2 * z * z * gap
def singularCeiling (P : Profile) : ℕ := singularNumerator P / gap + 1
def residualMixed (P Q : Profile) : Fin 3 → ℕ :=
  ![P.slopeCap * Q.seedCap + P.seedCap * Q.slopeCap,
    P.yCap * Q.seedCap + P.seedCap * Q.yCap, P.yCap * Q.slopeCap + P.slopeCap * Q.yCap]
def residualNumerator (P Q : Profile) : ℕ :=
  let c := residualMixed P Q
  U * (c 0 * (1 + 2 * w * max P.yCap Q.yCap) + c 1 * (w * (2 * max P.slopeCap Q.slopeCap - 1)) +
    c 2 * (2 * w * max P.seedCap Q.seedCap + 1)) + (errors + 1) * gap * c 2

def fixedSingularCost : ℕ := singularCeiling profileFinalMeet
def firstResidualRegularCost : ℕ := residualNumerator profileA profileB / gap
def firstResidualSingularCeiling : ℕ := singularCeiling profileB
def secondResidualRegularCost : ℕ := residualNumerator profileABMeet profileC / gap
def secondResidualSingularCeiling : ℕ := singularCeiling profileABMeet
def fixedCost : ℕ := fixedRegularCost + fixedSingularCost
def firstResidualCeiling : ℕ := firstResidualRegularCost + firstResidualSingularCeiling
def secondResidualCeiling : ℕ := secondResidualRegularCost + secondResidualSingularCeiling
def totalCost : ℕ := fixedCost + firstResidualCeiling + secondResidualCeiling

theorem fixed_ledger_values :
    fixedFlag = ⟨1169, 44, 11⟩ ∧ direction = ⟨2338, 87, 21⟩ ∧
    E = 9622955805 ∧ U = 131073 ∧
    degreeCost = 105531405322971842 ∧ unitCost = 76558451996587441 ∧
    fixedProperTailCost = 271280389332219760 ∧ identityZDegree = 276826187 ∧
    identityYZDegree = 6865472678 ∧ fixedIdentityYZCost = 1470385960010996 ∧
    fixedRegularCost = 272750775292230756 := by decide

theorem residual_values :
    residualMixed profileA profileB = ![1214025, 5459340, 2697] ∧
    residualMixed profileABMeet profileC = ![1020240, 5459146, 1313] ∧
    residualNumerator profileA profileB = 13720760636881944747 ∧
    residualNumerator profileABMeet profileC = 8347715426177579720 := by decide

theorem six_cells_exact :
    fixedRegularCost = 272750775292230756 ∧ fixedSingularCost = 60639931336494 ∧
    firstResidualRegularCost = 269092561863969 ∧ firstResidualSingularCeiling = 668990176848261 ∧
    secondResidualRegularCost = 163716005926328 ∧ secondResidualSingularCeiling = 65216430349605 := by decide

theorem total_and_slack_exact : totalCost = 273978430398655413 ∧
    mcaBudget - totalCost = 1002296712739674 ∧ totalCost < mcaBudget := by decide

theorem residual_characteristic_gates :
    singularY profileB = 5513 ∧ singularZ profileB = 60025 ∧
    2 * singularY profileB * singularZ profileB < prime ∧
    singularY profileABMeet = 1254 ∧ singularZ profileABMeet = 25725 ∧
    2 * singularY profileABMeet * singularZ profileABMeet < prime ∧
    singularY profileFinalMeet = 1166 ∧ singularZ profileFinalMeet = 25725 ∧
    2 * singularY profileFinalMeet * singularZ profileFinalMeet < prime ∧
    (1 + w * (direction.yz + direction.all)) * fixedFlag.all +
      (fixedFlag.yz + fixedFlag.all) * (w * direction.all) < prime := by decide

theorem first_tail_characteristic_gates :
    (fixedFlag.yz + fixedFlag.all) * firstTailFlag.all +
      (firstTailFlag.yz + firstTailFlag.all) * fixedFlag.all = 307101707 ∧
    (fixedFlag.yz + fixedFlag.all) * firstTailFlag.all +
      (firstTailFlag.yz + firstTailFlag.all) * fixedFlag.all < prime ∧
    (fixedFlag.yz + fixedFlag.all) * identityFlag.all +
      (identityFlag.yz + identityFlag.all) * fixedFlag.all = 307104050 ∧
    (fixedFlag.yz + fixedFlag.all) * identityFlag.all +
      (identityFlag.yz + identityFlag.all) * fixedFlag.all < prime ∧
    2 * (fixedFlag.zOnly + fixedFlag.yz + fixedFlag.all) *
      ((fiberFlag 1169 43 9).zOnly + (fiberFlag 1169 43 9).yz + (fiberFlag 1169 43 9).all) = 2994116 ∧
    2 * (fixedFlag.zOnly + fixedFlag.yz + fixedFlag.all) *
      ((fiberFlag 1169 43 9).zOnly + (fiberFlag 1169 43 9).yz + (fiberFlag 1169 43 9).all) < prime ∧
    (1 + (w + 1) * (2 * (43 + 9 + 3) - 2)) * fixedFlag.all +
      (fixedFlag.yz + fixedFlag.all) * ((2 * (9 + 2) - 2) * (w + 1)) = 299892747 ∧
    (1 + (w + 1) * (2 * (43 + 9 + 3) - 2)) * fixedFlag.all +
      (fixedFlag.yz + fixedFlag.all) * ((2 * (9 + 2) - 2) * (w + 1)) < prime := by decide

theorem total_lt_mcaBudget (total firstResidual secondResidual fixed : ℕ)
    (hpartition : total = firstResidual + secondResidual + fixed)
    (hfirst : firstResidual < firstResidualCeiling)
    (hsecond : secondResidual < secondResidualCeiling)
    (hfixed : fixed ≤ fixedCost) : total < mcaBudget := by
  have hsum : firstResidual + secondResidual + fixed < totalCost := by
    calc
      _ < firstResidualCeiling + secondResidual + fixed :=
        Nat.add_lt_add_right (Nat.add_lt_add_right hfirst secondResidual) fixed
      _ < firstResidualCeiling + secondResidualCeiling + fixed :=
        Nat.add_lt_add_right (Nat.add_lt_add_left hsecond firstResidualCeiling) fixed
      _ ≤ firstResidualCeiling + secondResidualCeiling + fixedCost :=
        Nat.add_le_add_left hfixed (firstResidualCeiling + secondResidualCeiling)
      _ = totalCost := by unfold totalCost; ring
  calc
    total = _ := hpartition
    _ < totalCost := hsum
    _ < mcaBudget := total_and_slack_exact.2.2

#print axioms interpolation_gates
#print axioms six_cells_exact
#print axioms total_and_slack_exact
#print axioms total_lt_mcaBudget
end ProximityPrize.SubmissionLower.ContactMovingParameters6732Research
