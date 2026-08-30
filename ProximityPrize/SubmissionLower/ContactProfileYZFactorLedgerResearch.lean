import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualTerminalIncidenceResearch
import ProximityPrize.SubmissionLower.ContactRobustFixedMeet6656Research
namespace ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch
open scoped Classical BigOperators
open ContactIdentityResidualIterationResearch
open ContactIdentityResidualTerminalIncidenceResearch
open ContactResidualSupportParametersResearch
open ContactRobustFixedMeet6656Research
open ContactInterpolation ContactSelectedSeedDecomposition
open ContactRegularFactorFlag6600Research
open ContactPrimeSeedIncidence ContactFlagBezout6543Research
set_option maxHeartbeats 1500000
set_option maxRecDepth 50000
def factorPrimaryForDirection
    (p:Profile) (direction flag:FlagDegree):ℕ:=
  flagMixed flag direction direction*p.degreeIncidence^2+
    2*flagMixed flag direction unitYZFlag*
      p.degreeIncidence*p.unitIncidence+
    flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence^2
def factorZTailForDirection
    (p:Profile) (direction flag:FlagDegree):ℕ:=
  (p.errors+1)*p.gap*
    (flagMixed flag direction unitZFlag*p.degreeIncidence+
      flagMixed flag unitYZFlag unitZFlag*p.unitIncidence)
def factorYZTailForDirection
    (p:Profile) (direction flag:FlagDegree):ℕ:=
  (p.errors+1)*p.gap*
    (flagMixed flag direction unitYZFlag*p.degreeIncidence+
      flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence)
def factorRegularLedgerYZForDirection
    (p:Profile) (direction flag:FlagDegree):ℕ:=
  factorPrimaryForDirection p direction flag+
    factorZTailForDirection p direction flag+
    factorYZTailForDirection p direction flag
def factorYZTail (p:Profile) (flag:FlagDegree):ℕ:=
  factorYZTailForDirection p p.agreementDirection flag
def factorRegularLedgerYZ (p:Profile) (flag:FlagDegree):ℕ:=
  factorRegularLedgerYZForDirection p p.agreementDirection flag
def regularNumeratorYZ (p:Profile):ℕ:=
  factorRegularLedgerYZ p p.rectangularSurfaceFlag
theorem factorRegularLedgerYZForDirection_projection_decomposition
    (p:Profile) (direction flag:FlagDegree):
    factorRegularLedgerYZForDirection p direction flag=
      flag.zOnly*factorRegularLedgerYZForDirection p direction unitZFlag+
      flag.yz*factorRegularLedgerYZForDirection p direction unitYZFlag+
      flag.all*factorRegularLedgerYZForDirection p direction unitAllFlag:=by
  cases flag
  simp [factorRegularLedgerYZForDirection,factorPrimaryForDirection,
    factorZTailForDirection,factorYZTailForDirection,flagMixed,
    unitZFlag,unitYZFlag,unitAllFlag]
  ring
theorem sum_factorRegularLedgerYZForDirection_le_flag
    {I:Type} [Fintype I] (p:Profile) (direction:FlagDegree)
    (flag:I → FlagDegree) (cap:FlagDegree)
    (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
    (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
    (hall:(∑ i,(flag i).all) ≤ cap.all):
    (∑ i,factorRegularLedgerYZForDirection p direction (flag i)) ≤
      factorRegularLedgerYZForDirection p direction cap:=by
  classical
  calc
    (∑ i,factorRegularLedgerYZForDirection p direction (flag i))=
        ∑ i,((flag i).zOnly*factorRegularLedgerYZForDirection p direction unitZFlag+
          (flag i).yz*factorRegularLedgerYZForDirection p direction unitYZFlag+
          (flag i).all*factorRegularLedgerYZForDirection p direction unitAllFlag):=by
      apply Finset.sum_congr rfl
      intro i _
      exact factorRegularLedgerYZForDirection_projection_decomposition p direction (flag i)
    _=(∑ i,(flag i).zOnly)*factorRegularLedgerYZForDirection p direction unitZFlag+
        (∑ i,(flag i).yz)*factorRegularLedgerYZForDirection p direction unitYZFlag+
        (∑ i,(flag i).all)*factorRegularLedgerYZForDirection p direction unitAllFlag:=by
      simp only [Finset.sum_add_distrib,Finset.sum_mul]
    _ ≤ cap.zOnly*factorRegularLedgerYZForDirection p direction unitZFlag+
        cap.yz*factorRegularLedgerYZForDirection p direction unitYZFlag+
        cap.all*factorRegularLedgerYZForDirection p direction unitAllFlag:=
      Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_right _ hz)
          (Nat.mul_le_mul_right _ hyz))
        (Nat.mul_le_mul_right _ hall)
    _=factorRegularLedgerYZForDirection p direction cap:=
      (factorRegularLedgerYZForDirection_projection_decomposition p direction cap).symm
theorem factorRegularLedgerYZ_projection_decomposition
    (p:Profile) (flag:FlagDegree):
    factorRegularLedgerYZ p flag=
      flag.zOnly*factorRegularLedgerYZ p unitZFlag+
      flag.yz*factorRegularLedgerYZ p unitYZFlag+
      flag.all*factorRegularLedgerYZ p unitAllFlag:=
  factorRegularLedgerYZForDirection_projection_decomposition
    p p.agreementDirection flag
theorem sum_factorRegularLedgerYZ_le_flag
    {I:Type} [Fintype I] (p:Profile)
    (flag:I → FlagDegree) (cap:FlagDegree)
    (hz:(∑ i,(flag i).zOnly) ≤ cap.zOnly)
    (hyz:(∑ i,(flag i).yz) ≤ cap.yz)
    (hall:(∑ i,(flag i).all) ≤ cap.all):
    (∑ i,factorRegularLedgerYZ p (flag i)) ≤
      factorRegularLedgerYZ p cap:=
  sum_factorRegularLedgerYZForDirection_le_flag p p.agreementDirection
    flag cap hz hyz hall
noncomputable section
variable {K Omega Iota:Type} [Field K] [Field Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {pchar:ℕ} [CharP Omega pchar] {flag:FlagDegree}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem sum_factor_counts_rectangularYZ_le
    (p:Profile) (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0)
    (hw:0 < p.w)
    (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
      p.seedTotalCap p.slopeCap)
    (count:RegularIndex Q → ℕ)
    (hcount:∀ F,count F*p.gap^2 ≤
      factorRegularLedgerYZ p (regularFlag Q F)):
    (∑ F,count F)*p.gap^2 ≤ regularNumeratorYZ p:=by
  have hcaps:=regularFlag_budgets p Q hQ hw hbox
  calc
    (∑ F,count F)*p.gap^2=∑ F,count F*p.gap^2:=by
      rw [Finset.sum_mul]
    _ ≤ ∑ F,factorRegularLedgerYZ p (regularFlag Q F):=
      Finset.sum_le_sum (fun F _↦hcount F)
    _ ≤ factorRegularLedgerYZ p p.rectangularSurfaceFlag:=
      sum_factorRegularLedgerYZ_le_flag p (regularFlag Q)
        p.rectangularSurfaceFlag hcaps.1 hcaps.2.1 hcaps.2.2
    _=regularNumeratorYZ p:=rfl
def factorDegreeCostYZ (p:Profile) (direction:FlagDegree)
    (flag:FlagDegree):ℕ:=
  (flagMixed flag direction direction*
      p.degreeIncidence+
    flagMixed flag direction unitYZFlag*p.unitIncidence)+
  (p.errors+1)*p.gap*
    (flagMixed flag direction unitZFlag+
      flagMixed flag direction unitYZFlag)
def factorUnitCostYZ (p:Profile) (direction:FlagDegree)
    (flag:FlagDegree):ℕ:=
  (flagMixed flag direction unitYZFlag*p.degreeIncidence+
    flagMixed flag unitYZFlag unitYZFlag*p.unitIncidence)+
  (p.errors+1)*p.gap*
    (flagMixed flag unitYZFlag unitZFlag+
      flagMixed flag unitYZFlag unitYZFlag)
theorem incidence_cost_eq_factorRegularLedgerYZ
    (p:Profile) (direction flag:FlagDegree)
    :
    p.degreeIncidence*factorDegreeCostYZ p direction flag+
      p.unitIncidence*factorUnitCostYZ p direction flag=
      factorRegularLedgerYZForDirection p direction flag:=by
  simp only [factorDegreeCostYZ,factorUnitCostYZ]
  simp only [factorRegularLedgerYZForDirection,factorPrimaryForDirection,
    factorZTailForDirection,factorYZTailForDirection]
  ring
theorem recursive_scaled_factorYZ
    (hphi:Function.Injective phi)
    (p:Profile) (support:ResidualSupportParameters)
    (direction:FlagDegree)
    (S:ResidualStage phi Gamma x pchar p.errors flag p.w support)
    (hwa:p.w < p.agreements)
    (hagreement:∀ gamma∈Gamma,
      p.agreements ≤ (S.agreementFiber gamma).card)
    (hfiber:∀ D:S.TerminalDescendant,∀ i∈D.stage.nodes,
      ¬ D.stage.G∣agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i) →
      (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card*p.gap ≤
        D.degree*factorDegreeCostYZ p direction flag+
          factorUnitCostYZ p direction flag)
    (hdegree:∀ k ≤ p.w,
      (S.nodes.card-k)*p.gap*(p.w-k) ≤
        p.degreeIncidence*(p.agreements-k))
    (hunit:∀ k ≤ p.w,
      (S.nodes.card-k)*p.gap ≤
        p.unitIncidence*(p.agreements-k)):
    Gamma.card*p.gap^2 ≤
      factorRegularLedgerYZForDirection p direction flag:=by
  have h:=recursive_scaled_stratified_incidence_bound
    hphi S (factorDegreeCostYZ p direction flag)
      (factorUnitCostYZ p direction flag)
      p.degreeIncidence p.unitIncidence hwa hagreement
      (by simpa only [Profile.gap] using hfiber)
      (by simpa only [Profile.gap] using hdegree)
      (by simpa only [Profile.gap] using hunit)
  calc
    Gamma.card*p.gap^2 ≤
        p.degreeIncidence*factorDegreeCostYZ p direction flag+
          p.unitIncidence*factorUnitCostYZ p direction flag:=by
      simpa only [Profile.gap] using h
    _=factorRegularLedgerYZForDirection p direction flag:=
      incidence_cost_eq_factorRegularLedgerYZ p direction flag
end
end ProximityPrize.SubmissionLower.ContactProfileYZFactorLedgerResearch
