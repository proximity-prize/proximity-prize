import ProximityPrize.SubmissionLower.GM
import ProximityPrize.SubmissionLower.AM
namespace ProximityPrize.SubmissionLower.RCN329
open scoped Classical BigOperators
open RCN135 RCN136
open RCN159 RCN264
open RCN074
open RCN086 RCN243
open RCN238 RCN095
open RCN237 RCN046
open RCN341 RCN002
open RCN344
open RCN312
open RCN338
open RCN174
open RCN042
open RCN339
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 30000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
abbrev Omega (K:Type) [Field K]:=GenericField K
variable {Gamma:Finset K} {x:I → K} {p:ℕ}
variable [CharP (Omega K) p] {flag:FlagDegree}
variable {support:RCN275.ResidualSupportParameters}
abbrev FixedStage
   (phi:Polynomial K →+*Omega K:=polynomialEmbedding K):=
 ResidualStage phi Gamma x p RCN326.errors
   flag RCN326.w support
structure ProperDelayedTailCertificate
   (S:FixedStage (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
     (support:=support))
   (B:PrimeFlagBudgetFamily
     (G:=S.G)
     (T:=globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1))
     (H:=regularitySurface (polynomialEmbedding K) S.F) flag
     (RCN326.tailFlag
       (RCN326.w+1)))
   (multiplicity:FirstTailComponent S → ℕ) where
 branch:∀ C:FirstTailComponent S,
   (∃ delay,1 ≤ delay∧delay ≤ multiplicity C∧
     globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∉C.1∧
     (componentSeeds (Omega K) S.G
       (globalTailCut (polynomialEmbedding K) S.F
         (RCN326.w+1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         multiplicity C*B.weightedCost
           (RCN326.tailFlag
             (RCN326.w+2)) C)∨
   (∀ delay,globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1+delay)∈C.1)
theorem delayedTailMultiplicityProvider_of_certificates
   (S:FixedStage (Gamma:=Gamma) (x:=x) (p:=p) (flag:=flag)
     (support:=support))
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (baseFamily:∀ C:FirstTailComponent S,SeparableLiteralCoordinate C.1)
   (U:AdaptiveUnitProjectionFamily baseFamily flag
     (RCN326.tailFlag
       (RCN326.w+1)))
   (hyzTranscendental:∀ C:FirstTailComponent S,
     Transcendental (Omega K)
       (coordinateValue (Omega K) (CoordinateField (Omega K) C.1)
         (U.yzProjection C)))
   (bound seedCap slopeCap:ℕ)
   (hnodes:S.nodes.card=RCN326.agreements+
     RCN326.errors)
   (hagreement:∀ gamma∈Gamma,
     RCN326.agreements ≤
       (S.agreementFiber gamma).card)
   (hshort:RCN326.w+1 ≤ bound)
   (hchar:bound < p)
   (hbox:S.F∈globalCoefficientBox K bound
     RCN326.w seedCap slopeCap)
   (multiplicity:FirstTailComponent S → ℕ)
   (hone:∀ C,1 ≤ multiplicity C)
   (proper:ProperDelayedTailCertificate S U.toPrimeFlagBudgetFamily multiplicity)
   (resultants:RegularComponentWeightedInertiaResultantCertificate
     U.toPrimeFlagBudgetFamily multiplicity):
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1:=RCN326.tailFlag
       (RCN326.w+1))
     (tailFlag2:=RCN326.tailFlag
       (RCN326.w+2)) S):=by
 let B:=U.toPrimeFlagBudgetFamily
 let secondTail:=RCN326.tailFlag
   (RCN326.w+2)
 let cost:FirstTailComponent S → ℕ:=
   fun C => multiplicity C*B.weightedCost secondTail C
 have hyzPositive (C:FirstTailComponent S):1 ≤ B.yzCost C:=by
   change 1 ≤ coordinateDegree (Omega K) (CoordinateField (Omega K) C.1)
     (U.yzProjection C)
   exact one_le_coordinateDegree_of_transcendental_value
     (U.yzProjection C) (hyzTranscendental C)
 have hyzPole (C:FirstTailComponent S):∀ W:Finset
     (RCN346.Place (Omega K) (CoordinateField (Omega K) C.1)),
     (∑ v∈W,RCN295.exponentSetPoleWeight
       v.val (coordinate (Omega K) C.1)
       (RCN095.flagSupport
         RCN095.unitYZFlag)) ≤ (B.yzCost C:ℤ):=by
   exact U.toAdaptiveUnitPoleBudget.yzPole C
 have tangentCount (C:FirstTailComponent S)
     (hall:∀ delay,globalTailCut (polynomialEmbedding K) S.F
       (RCN326.w+1+delay)∈C.1):
     (componentSeeds (Omega K) S.G
       (globalTailCut (polynomialEmbedding K) S.F
         (RCN326.w+1))
       (regularitySurface (polynomialEmbedding K) S.F) Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (RCN326.errors+1)*B.yzCost C:=by
   exact tangent_component_card_le S C hfirstProper (baseFamily C)
     RCN326.agreements bound seedCap slopeCap
     hnodes hagreement (by decide) (by decide) hshort hchar hbox B
     (hyzPositive C) hall (hyzPole C)
 refine ⟨{
   budgetFamily:=B
   multiplicity:=multiplicity
   cost:=cost
   one_le_multiplicity:=hone
   tangentYZGate:=errors_succ_le_secondTail_yz
   cost_le:=fun C => le_rfl
   divisor_le:=resultants.divisor_le B multiplicity
   componentBound:=?_
   dichotomy:=?_}⟩
 · intro C
   rcases proper.branch C with hproper | htangent
   · exact hproper.choose_spec.2.2.2
   · exact (tangentCount C htangent).trans
       (tangentCost_le_multiplicity_secondTail_weightedCost
         B C (multiplicity C) (hone C))
 · intro C
   rcases proper.branch C with hproper | htangent
   · exact Or.inl ⟨hproper.choose,hproper.choose_spec.1,
       hproper.choose_spec.2.1,hproper.choose_spec.2.2.1⟩
   · exact Or.inr ⟨htangent,tangentCount C htangent⟩
end
end ProximityPrize.SubmissionLower.RCN329
