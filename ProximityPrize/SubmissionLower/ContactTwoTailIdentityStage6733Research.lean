import ProximityPrize.SubmissionLower.ContactProperDelayedTailCertificate6732Research
import ProximityPrize.SubmissionLower.ContactIdentityCurveProvider6731Research
import ProximityPrize.SubmissionLower.ContactFirstTailIdentityIncidence6731Research
import ProximityPrize.SubmissionLower.ContactTwoTailParameters6733Research
namespace ProximityPrize.SubmissionLower.ContactTwoTailIdentityStage6733Research
open ContactProperDelayedTailCertificate6732Research
open ContactGenericInitialPoint ContactGenericSurface ContactInterpolation
open ContactTaylorNumerators
open ContactIdentityCurveProvider6731Research
open ContactFirstTailIdentityIncidence6731Research
open ContactFirstTailCertificate6731Research
open ContactFlagBezout6543Research
open ContactMovingOuterBudget6719Research
open ContactTwoTailParameters6733Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 40000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {flag:FlagDegree}
variable [CharP (GenericField K) prime]
theorem identity_degree_direct_two_tail
    (flag:FlagDegree):
    (n-w)*(errors+1)*
        identityCurveDegree flag 1186 44 9 w ≤
      gap*flagMixed flag (tailFlag (w+1)) (tailFlag (w+2)):=by
  norm_num [identityCurveDegree,n,w,errors,agreements,gap,tailFlag,fixedFlag,
    finalMeet,direction,paddedCut,
    ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,
    add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
  omega
theorem identity_degree_exact (flag:FlagDegree):
    identityCurveDegree flag 1186 44 9 w=
      2752533*flag.zOnly+5505066*flag.yz+
        339741218*flag.all:=by
  norm_num [identityCurveDegree,w,paddedCut,
    ContactMovingPositiveLedger6719Research.centreFlag,
    ContactMovingPositiveLedger6719Research.directionFlag,
    flagMixed,unitZFlag,unitYZFlag,
    add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
  ring
theorem identity_stage_card_le
    (S:Stage K I Gamma x prime flag)
    (hTail:S.G∣globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hnodes:S.nodes.card=agreements+errors)
    (hagreement:∀ gamma∈Gamma,
      agreements ≤ (S.agreementFiber gamma).card)
    (hbox:S.F∈globalCoefficientBox K (41*agreements) w 1242 11)
    (hflag:flag.all ≤ 11∧flag.yz+flag.all ≤ 56∧
      flag.zOnly+flag.yz+flag.all ≤ 1242):
    Gamma.card ≤ flagMixed flag (tailFlag (w+1)) (tailFlag (w+2)):=by
  have hTailNumerator:S.G∣surfaceMap (polynomialEmbedding K)
      (numerator K S.F (w+1)):=
    (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
  have hprovider:=actual_identityCurveCountProvider S agreements hnodes
    hagreement (by decide) hTailNumerator (41*agreements) 1242 11
    (by decide) (by decide) (by decide) hbox
    (by
      refine ⟨hflag.2.1.trans_lt (by decide),hflag.1.trans_lt (by decide),
        hflag.2.2.trans_lt (by decide)⟩)
    (by
      have h:=hflag
      norm_num [prime,w] at h ⊢
      omega)
  let identityDegree:=identityCurveDegree flag 1186 44 9 w
  have hpositive:1 ≤ identityDegree:=by
    rw [show identityDegree=2752533*flag.zOnly+
        5505066*flag.yz+339741218*flag.all by
      exact identity_degree_exact flag]
    have hy:0 < S.G.degreeOf 1:=S.y_dependent
    have hdeg:=ContactFactoredFlagCount6676Research.degreeOf_le_flag_total
      S.G flag S.flag_support 1
    omega
  have hinc:=identity_surface_seed_bound S agreements identityDegree hprovider
    hagreement (by decide) (by rw [hnodes];decide) hpositive
  have hbudget:=identity_degree_direct_two_tail flag
  have hscaled:Gamma.card*gap ≤
      gap*flagMixed flag (tailFlag (w+1)) (tailFlag (w+2)):=by
    calc
      Gamma.card*gap=Gamma.card*(agreements-w):=rfl
      _ ≤ (S.nodes.card-w)*(errors+1)*identityDegree:=hinc
      _=(n-w)*(errors+1)*identityDegree:=by
        rw [hnodes]
        norm_num [n,agreements,errors]
      _ ≤ gap*flagMixed flag (tailFlag (w+1)) (tailFlag (w+2)):=
        hbudget
  apply Nat.le_of_mul_le_mul_right ?_ (by decide:0 < gap)
  simpa only [Nat.mul_comm] using hscaled
end
end ProximityPrize.SubmissionLower.ContactTwoTailIdentityStage6733Research
