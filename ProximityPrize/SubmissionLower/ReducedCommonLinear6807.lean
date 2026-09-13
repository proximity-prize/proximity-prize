/-
UNCOMPILED. The shared linear values are constructed for the actual reduced
family and transported to the ORIGINAL first-tail components. No new budget
family is chosen and no first-cut cost bound is assumed.
-/
import ProximityPrize.SubmissionLower.CommonLinearChannels6807
import ProximityPrize.SubmissionLower.BoundaryTailReduced

namespace ProximityPrize.SubmissionLower.ReducedCommonLinear6807
open scoped Classical BigOperators
open RCN159 RCN263 RCN086 RCN327
open RCN135 RCN136 RCN264 RCN243 RCN095 RCN237 RCN198 RCN275 RCN244
open RCN334 RCN332 RCN336 RCN338 RCN199 RCN207 RCN313 RCN341 RCN030
open LocatorHybridTransportC2 CommonLinearChannels6807 BoundaryTailReduced
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {stageErrorCap a b s : ℕ}

def reduced_common
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    CommonLinearValues (reducedUnitFamily S hp hc hm) := by
  let A := reducedActiveGeometry S hp hc hm
  exact of_active_nested A.base A.hactive A.hZ
    (RCN315.residualStage_pderiv_one_ne_zero_of_support S) A.data
    S.irreducible_G (reducedFirstCut_proper S hp)
    ((support_subset_flagSupport_iff flag S.G).2 S.flag_support)
    ((support_subset_flagSupport_iff
      (reducedResidualAgreementFlag (support a b s) (w+1))
      (reducedFirstCut S)).2 (reducedFirstCut_in_flag S))

def original_common
    (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag
      w (support a b s))
    (hp : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hc : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hm : flagMixed flag (reducedResidualAgreementFlag (support a b s) (w+1)) unitZFlag < p) :
    CommonLinearValues (unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S)
      (reducedUnitFamily S hp hc hm) (reducedBaseOrd S hp hc hm)) :=
  of_congruent_cut (ordinary_sub_reducedFirstCut_dvd S)
    (reducedUnitFamily S hp hc hm) (reducedBaseOrd S hp hc hm)
    (reduced_common S hp hc hm)

end
end ProximityPrize.SubmissionLower.ReducedCommonLinear6807
