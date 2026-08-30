import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.U
import ProximityPrize.SubmissionLower.Z4
import ProximityPrize.SubmissionLower.AG
namespace ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
open scoped Classical BigOperators
open ContactInterpolation ContactTranslation ContactSelectedSeedDecomposition
open ContactImplicitContactLift ContactImplicitPairBudgets
open ContactSingularAuxiliary ContactPrimeSeedIncidence
open ContactRegularFactorFlag6600Research
open ContactFlagBezout6543Research
open ContactGlobalSelectedFamilies6600Research
open ContactSingularBranch6600Research
open ContactTightSingularLedgerResearch
open ContactSingularBranchParameterizedResearch
open ContactRobustFixedMeet6656Research
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 40000
structure FixedParameterAlignment (p:Profile)
   (t:ContactTightSingularLedgerResearch.TightParameters):Prop where
 n:t.n=p.n
 w:t.w=p.w
 agreements:t.a=p.agreements
 weightedCap:t.D=p.weightedCap
 seedTotalCap:t.L=p.seedTotalCap
 slopeCap:t.s=p.slopeCap
namespace FixedParameterAlignment
theorem errors {p:Profile}
   {t:ContactTightSingularLedgerResearch.TightParameters}
   (A:FixedParameterAlignment p t):t.errors=p.errors:=by
 simp only [ContactTightSingularLedgerResearch.TightParameters.errors,
   Profile.errors,A.n,A.agreements]
theorem gap {p:Profile}
   {t:ContactTightSingularLedgerResearch.TightParameters}
   (A:FixedParameterAlignment p t):t.gap=p.gap:=by
 simp only [ContactTightSingularLedgerResearch.TightParameters.gap,
   Profile.gap,A.w,A.agreements]
end FixedParameterAlignment
variable {K Iota:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem card_le_regular_sum_add_singular
   (p:Profile) {prime:ℕ}
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (hs:1 ≤ p.slopeCap) (hsSmall:p.slopeCap < prime)
   (hw:1 ≤ p.w)
   (hDw:p.w < (2*p.slopeCap-1)*p.weightedCap)
   (hj:1 ≤ (2*p.slopeCap-1)*p.seedTotalCap)
   (hjSmall:(2*p.slopeCap-1)*p.seedTotalCap < prime)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0):
   Gamma.card ≤
     (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=by
 classical
 have hdecomp:=selected_seed_decomposition Q hQ
   p.weightedCap p.w p.seedTotalCap p.slopeCap prime
   hs hsSmall hw hDw hj hjSmall hbox Gamma selected hsolution
 let regularUnion:=Finset.univ.biUnion (regularSeeds Q selected Gamma)
 have hsub:Gamma ⊆ regularUnion ∪ singularSeeds Q selected Gamma:=by
   intro gamma hgamma
   by_cases hexc:gamma∈
       exceptionalSeeds (singularAuxiliary Q) Gamma selected
   · apply Finset.mem_union.mpr
     right
     apply Finset.mem_union.mpr
     right
     exact hexc
   · obtain ⟨F,hF,hreg⟩ | ⟨q,hq,himp⟩:=
       hdecomp.2.1 gamma hgamma hexc
     · apply Finset.mem_union.mpr
       left
       apply Finset.mem_biUnion.mpr
       exact ⟨⟨F,hF⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,hreg⟩⟩
     · apply Finset.mem_union.mpr
       right
       apply Finset.mem_union.mpr
       left
       apply Finset.mem_biUnion.mpr
       exact ⟨⟨q,hq⟩,Finset.mem_univ _,
         Finset.mem_filter.mpr ⟨hgamma,himp⟩⟩
 calc
   Gamma.card ≤ (regularUnion ∪ singularSeeds Q selected Gamma).card:=
     Finset.card_le_card hsub
   _ ≤ regularUnion.card+(singularSeeds Q selected Gamma).card:=
     Finset.card_union_le _ _
   _ ≤ (∑ F:RegularIndex Q,
         (regularSeeds Q selected Gamma F).card)+
       (singularSeeds Q selected Gamma).card:=
     Nat.add_le_add_right Finset.card_biUnion_le _
theorem global_count_le_regular_div_add_tight_countCap
   (p:Profile)
   (t:ContactTightSingularLedgerResearch.TightParameters)
   (A:FixedParameterAlignment p t)
   {prime regularNumerator:ℕ}
   (Q:MvPolynomial (Fin 4) K) (hQ:Q≠0) [CharP K prime]
   (hbox:Q∈globalCoefficientBox K p.weightedCap p.w
     p.seedTotalCap p.slopeCap)
   (hs:1 ≤ p.slopeCap) (hsSmall:p.slopeCap < prime)
   (hw:1 ≤ p.w) (hchar:p.w < prime)
   (hDw:p.w < (2*p.slopeCap-1)*p.weightedCap)
   (hj:1 ≤ (2*p.slopeCap-1)*p.seedTotalCap)
   (hjSmall:(2*p.slopeCap-1)*p.seedTotalCap < prime)
   (hjYSmall:t.implicitYCap < prime)
   (hmixedSmall:2*t.implicitYCap*t.algebraicCap < prime)
   (hwa:p.w < p.agreements) (han:p.agreements ≤ p.n)
   (selected:K → Polynomial K) (Gamma:Finset K)
   (nodes:Finset Iota) (x u0 u1:Iota → K)
   (hinj:Set.InjOn x nodes) (hnodes:nodes.card=p.n)
   (hdegree:∀ gamma∈Gamma,
     (selected gamma).natDegree ≤ p.w)
   (hsolution:∀ gamma∈Gamma,
     specialization K (selected gamma) gamma Q=0)
   (hagreement:∀ gamma∈Gamma,
     p.agreements ≤ (nodes.filter (fun i↦
       (selected gamma).eval (x i)=u0 i+gamma*u1 i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Gamma p.w p.errors)
   (regularFlagFor:RegularIndex Q → FlagDegree)
   (regularLedger:FlagDegree → ℕ)
   (hregularAggregate:
     ∀ count:RegularIndex Q → ℕ,
       (∀ F,count F*p.gap^2 ≤ regularLedger (regularFlagFor F)) →
       (∑ F,count F)*p.gap^2 ≤ regularNumerator)
   (hregular:∀ F:RegularIndex Q,
     (regularSeeds Q selected Gamma F).card*p.gap^2 ≤
       regularLedger (regularFlagFor F)):
   Gamma.card ≤ regularNumerator/p.gap^2+t.countCap:=by
 have hcover:=card_le_regular_sum_add_singular p Q hQ hbox
   hs hsSmall hw hDw hj hjSmall selected Gamma hsolution
 have hreg:=hregularAggregate
   (fun F:RegularIndex Q↦(regularSeeds Q selected Gamma F).card)
   hregular
 have hboxT:Q∈globalCoefficientBox K t.D t.w t.L t.s:=by
   simpa only [A.weightedCap,A.w,A.seedTotalCap,A.slopeCap] using hbox
 have hsing:=
   ContactSingularBranchParameterizedResearch.TightParameters.singularSeeds_tight_gap_bound
     t Q hQ hboxT
   (by simpa only [A.slopeCap] using hs)
   (by simpa only [A.slopeCap] using hsSmall)
   (by simpa only [A.w] using hw)
   (by simpa only [A.w] using hchar)
   (by
     simpa only [ContactTightSingularLedgerResearch.TightParameters.kappa,
       A.w,A.weightedCap,A.slopeCap]
       using hDw)
   (by simpa only
     [ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
       ContactTightSingularLedgerResearch.TightParameters.kappa,
       A.seedTotalCap,A.slopeCap] using hj)
   hjYSmall
   (by simpa only
     [ContactTightSingularLedgerResearch.TightParameters.algebraicCap,
       ContactTightSingularLedgerResearch.TightParameters.kappa,
       A.seedTotalCap,A.slopeCap] using hjSmall)
   hmixedSmall
   (by simpa only [A.w,A.agreements] using hwa)
   (by simpa only [A.agreements,A.n] using han)
   selected Gamma nodes x u0 u1 hinj
   (by simpa only [A.n] using hnodes)
   (by simpa only [A.w] using hdegree)
   (by simpa only [A.agreements] using hagreement)
   (by simpa only [A.w,A.errors] using hnoPencil)
 have hpgap:0 < p.gap:=by
   simpa only [Profile.gap] using Nat.sub_pos_of_lt hwa
 have htgap:0 < t.gap:=by simpa only [A.gap] using hpgap
 have hregCount:
     (∑ F:RegularIndex Q,(regularSeeds Q selected Gamma F).card) ≤
       regularNumerator/p.gap^2:=
   (Nat.le_div_iff_mul_le (pow_pos hpgap 2)).2 hreg
 have hsingCount:(singularSeeds Q selected Gamma).card ≤ t.countCap:=
   t.count_le_countCap _ htgap hsing
 exact hcover.trans (Nat.add_le_add hregCount hsingCount)
end
end ProximityPrize.SubmissionLower.ContactProfileFixedSelectedCombinerResearch
