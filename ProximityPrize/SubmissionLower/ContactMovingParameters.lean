import ProximityPrize.SubmissionLower.ContactStackedParameters
import ProximityPrize.SubmissionLower.ContactMovingReducedFactorLedger

/-! Exact arithmetic for the conditional 67.32 reduced-first-tail row. -/
namespace ProximityPrize.SubmissionLower.ContactMovingParameters
open ContactFlagInterpolation ContactFlagRankKernel
open ContactFlagBezout ContactMovingPositiveLedger
open ContactResidualSupportParameters
open ContactMovingReducedPositiveLedger
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def n : ℕ := 262144
def w : ℕ := 131071
def prime : ℕ := 2130706433
def errors : ℕ := 80082
def agreements : ℕ := n-errors
def gap : ℕ := agreements-w
def listBudget : ℕ := 1000000000
def capacity : ℕ := prime^6/2^128
def mcaBudget : ℕ := capacity-listBudget

structure Profile where
  multiplicity : ℕ
  seedCap : ℕ
  slopeCap : ℕ
  deriving DecidableEq
def profileA : Profile := ⟨43,38583,11⟩
def profileB : Profile := ⟨81,1222,25⟩
def profileC : Profile := ⟨40,91386,12⟩
def profileABMeet : Profile := ⟨43,1222,11⟩
def profileFinalMeet : Profile := ⟨40,1222,11⟩
namespace Profile
def weightedCap (P : Profile) : ℕ := P.multiplicity*agreements
def yCap (P : Profile) : ℕ := (P.weightedCap-1)/w
def coefficients (P : Profile) : ℕ := coefficientCount P.weightedCap w P.seedCap P.slopeCap
def localRank (P : Profile) : ℕ := localRankBound P.multiplicity P.seedCap P.slopeCap
def totalRank (P : Profile) : ℕ := n*P.localRank
def characteristicCap (P : Profile) : ℕ := (2*P.slopeCap-1)*P.weightedCap
end Profile

theorem base_values : agreements=182062 ∧ gap=50991 ∧
    capacity=274980728111395087 ∧ mcaBudget=274980727111395087 ∧
    mcaBudget+listBudget=capacity := by decide
theorem profileA_coefficients_exact : profileA.coefficients=91190645134027 := by
  change coefficientCount (43*182062) 131071 38583 11=91190645134027
  rw [ContactStackedParameters.coefficientCount_eq_sum_range_of_weighted_cutoff
    (43*182062) 131071 38583 11 60 (by decide) (by decide)]
  decide
theorem profileB_coefficients_exact : profileB.coefficients=20395196377088 := by
  change coefficientCount (81*182062) 131071 1222 25=20395196377088
  rw [ContactStackedParameters.coefficientCount_eq_sum_range_of_weighted_cutoff
    (81*182062) 131071 1222 25 113 (by decide) (by decide)]
  decide
theorem profileC_coefficients_exact : profileC.coefficients=196166579454729 := by
  change coefficientCount (40*182062) 131071 91386 12=196166579454729
  rw [ContactStackedParameters.coefficientCount_eq_sum_range_of_weighted_cutoff
    (40*182062) 131071 91386 12 56 (by decide) (by decide)]
  decide
theorem profileA_rank_exact : profileA.localRank=347864704 := by decide
theorem profileB_rank_exact : profileB.localRank=77801373 := by decide
theorem profileC_rank_exact : profileC.localRank=748316114 := by decide
theorem interpolation_gates : profileA.totalRank<profileA.coefficients ∧
    profileB.totalRank<profileB.coefficients ∧ profileC.totalRank<profileC.coefficients := by
  change n*profileA.localRank<profileA.coefficients ∧ n*profileB.localRank<profileB.coefficients ∧
    n*profileC.localRank<profileC.coefficients
  rw [profileA_coefficients_exact,profileA_rank_exact,
    profileB_coefficients_exact,profileB_rank_exact,profileC_coefficients_exact,profileC_rank_exact]
  decide

def fixedSupport : ResidualSupportParameters :=
  ContactMovingAgreementCertificate.support 1167 43 9

def fixedProfileForLedger : ContactRobustFixedMeet.Profile :=
  ⟨262144, 131071, 182062, 7282480, 1222, 11⟩

def fixedFlag : FlagDegree := surfaceFlag 1167 43 9
def direction : FlagDegree := directionFlag 1167 43 9
def centre : FlagDegree := centreFlag 1167 43 9
def U : ℕ := n-w

def degreeCost : ℕ :=
  ContactMovingReducedFactorLedger.factorDegreeCost
    fixedProfileForLedger fixedSupport 1167 43 9 fixedFlag

def unitCost : ℕ :=
  ContactMovingReducedFactorLedger.factorUnitCost
    fixedProfileForLedger fixedSupport 1167 43 9 fixedFlag

def fixedProperTailCost : ℕ := ((w+1)*degreeCost+unitCost)/gap+1

def identityFlag : FlagDegree := centre+(w+1) • direction
def identityZDegree : ℕ := flagMixed fixedFlag identityFlag unitZFlag
def identityYZDegree : ℕ := flagMixed fixedFlag identityFlag unitYZFlag
def fixedIdentityYZCost : ℕ := U*(errors+1)*(identityZDegree+identityYZDegree)/gap+1
def fixedRegularCost : ℕ := fixedProperTailCost+fixedIdentityYZCost

def singularY (P : Profile) : ℕ := (P.characteristicCap-1)/w
def singularZ (P : Profile) : ℕ := (2*P.slopeCap-1)*P.seedCap
def singularNumerator (P : Profile) : ℕ :=
  let y:=singularY P; let z:=singularZ P
  U*((1+2*w*y)*z+w*(2*y*z)+(2*w*z+1)*y)+(errors+1)*gap*y+2*z*z*gap
def singularCeiling (P : Profile) : ℕ := singularNumerator P/gap+1
def residualMixed (P Q : Profile) : Fin 3 → ℕ :=
  ![P.slopeCap*Q.seedCap+P.seedCap*Q.slopeCap,
    P.yCap*Q.seedCap+P.seedCap*Q.yCap,P.yCap*Q.slopeCap+P.slopeCap*Q.yCap]
def residualNumerator (P Q : Profile) : ℕ :=
  let c:=residualMixed P Q
  U*(c 0*(1+2*w*max P.yCap Q.yCap)+c 1*(w*(2*max P.slopeCap Q.slopeCap-1))+
    c 2*(2*w*max P.seedCap Q.seedCap+1))+(errors+1)*gap*c 2
def fixedSingularCost : ℕ := singularCeiling profileFinalMeet
def firstResidualRegularCost : ℕ := residualNumerator profileA profileB/gap
def firstResidualSingularCeiling : ℕ := singularCeiling profileB
def secondResidualRegularCost : ℕ := residualNumerator profileABMeet profileC/gap
def secondResidualSingularCeiling : ℕ := singularCeiling profileABMeet
def fixedCost : ℕ := fixedRegularCost+fixedSingularCost
def firstResidualCeiling : ℕ := firstResidualRegularCost+firstResidualSingularCeiling
def secondResidualCeiling : ℕ := secondResidualRegularCost+secondResidualSingularCeiling
def totalCost : ℕ := fixedCost+firstResidualCeiling+secondResidualCeiling

theorem six_cells_exact :
    fixedRegularCost=273593170675834005 ∧ fixedSingularCost=60489048372185 ∧
    firstResidualRegularCost=216720566639304 ∧ firstResidualSingularCeiling=667325631931636 ∧
    secondResidualRegularCost=163704523661892 ∧ secondResidualSingularCeiling=65054160163108 := by decide
theorem total_and_slack_exact : totalCost=274766464606602130 ∧
    mcaBudget-totalCost=214262504792957 ∧ totalCost<mcaBudget := by decide

/-- Arithmetic consumer; construction of these three cell bounds is external. -/
theorem total_lt_mcaBudget (total firstResidual secondResidual fixed : ℕ)
    (hpartition : total=firstResidual+secondResidual+fixed)
    (hfirst : firstResidual<firstResidualCeiling)
    (hsecond : secondResidual<secondResidualCeiling)
    (hfixed : fixed≤fixedCost) : total<mcaBudget := by
  have hsum : firstResidual+secondResidual+fixed<totalCost := by
    calc
      _ < firstResidualCeiling+secondResidual+fixed :=
        Nat.add_lt_add_right (Nat.add_lt_add_right hfirst secondResidual) fixed
      _ < firstResidualCeiling+secondResidualCeiling+fixed :=
        Nat.add_lt_add_right (Nat.add_lt_add_left hsecond firstResidualCeiling) fixed
      _ ≤ firstResidualCeiling+secondResidualCeiling+fixedCost :=
        Nat.add_le_add_left hfixed (firstResidualCeiling+secondResidualCeiling)
      _ = totalCost := by unfold totalCost; ring
  calc
    total = _ := hpartition
    _ < totalCost := hsum
    _ < mcaBudget := total_and_slack_exact.2.2

end ProximityPrize.SubmissionLower.ContactMovingParameters
