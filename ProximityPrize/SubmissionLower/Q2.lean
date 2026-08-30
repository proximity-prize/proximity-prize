import ProximityPrize.SubmissionLower.P9
namespace ProximityPrize.SubmissionLower.RCN335
open scoped Classical BigOperators
open RCN135 RCN136
open RCN159 RCN264
open RCN074
open RCN086 RCN243
open RCN238 RCN095
open RCN237
open RCN198
open RCN275
open RCN244
open RCN327
open RCN263
open RCN334
open RCN332
open RCN336
open RCN312
open RCN339
open RCN330
open RCN174 RCN319
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p]
variable {stageErrorCap : ℕ}
/- Agreement and error parameters are explicit data on the general path. -/
theorem exists_delayedTailMultiplicityProvider_of_reducedGeneral
   {a b s : ℕ}
   (agreementCap : ℕ)
   (S : ResidualStage (polynomialEmbedding K) Gamma x p stageErrorCap flag w
     (support a b s))
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap : ℕ)
   (hnodes : S.nodes.card = agreementCap + stageErrorCap)
   (hagreement : ∀ gamma ∈ Gamma, agreementCap ≤ (S.agreementFiber gamma).card)
   (hwa : w < agreementCap)
   (hshort : w + 1 ≤ bound) (hchar : bound < p)
   (hbox : S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate : stageErrorCap + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1 := reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2 := reducedResidualAgreementFlag (support a b s) (w + 2)) S) := by
 classical
 let supp := support a b s
 let S0 := loosenStageGeneral S
 let T := globalTailCut (polynomialEmbedding K) S.F (w + 1)
 let H := regularitySurface (polynomialEmbedding K) S.F
 let secondFlag := reducedResidualAgreementFlag supp (w + 2)
 let B := reducedBudgetFamily S hfirstProper hflagChar hmixed
 let multiplicity := reducedMultiplicityGeneral S hfirstProper
 have hone : ∀ C, 1 ≤ multiplicity C := by
   exact loosenStageGeneral_one_le_localMultiplicity S hfirstProper
 have tangentCount (C : FirstTailComponent S)
     (hall : ∀ delay, globalTailCut (polynomialEmbedding K) S.F
       (w + 1 + delay) ∈ C.1) :
     (componentSeeds (GenericField K) S.G T H Gamma
       (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C := by
   exact tangent_component_card_le S C hfirstProper
     (reducedBaseOrd S hfirstProper hflagChar hmixed C)
     agreementCap bound seedCap slopeCap hnodes hagreement
     hwa (by norm_num [w])
     hshort hchar hbox B
     (reducedBudgetFamily_yzPositive S hfirstProper hflagChar hmixed C)
     hall (reducedBudgetFamily_yzPole S hfirstProper hflagChar hmixed C)
 have branchBound (C : FirstTailComponent S) :
     ((∃ delay, 1 ≤ delay ∧ delay ≤ multiplicity C ∧
         globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay) ∉ C.1 ∧
         (componentSeeds (GenericField K) S.G T H Gamma
           (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
             multiplicity C * B.weightedCost secondFlag C) ∨
       (∀ delay, globalTailCut (polynomialEmbedding K) S.F
         (w + 1 + delay) ∈ C.1)) := by
   have dichotomy := local_order_tail_dichotomy S0
     (canonicalLocalDVRFamily S0 hfirstProper) C hfirstProper
   rcases dichotomy.2 with hproper | htangent
   · left
     obtain ⟨delay, hdelay, hdelayMu, htail⟩ := hproper
     have hzero : ∀ gamma ∈ componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C,
         MvPolynomial.aeval (selectedPoint (polynomialEmbedding K) S.selected gamma)
           (globalTailCut (polynomialEmbedding K) S.F (w + 1 + delay)) = 0 := by
       intro gamma hgamma
       have hGamma := componentSeeds_subset (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C hgamma
       exact selected_globalTailCut_zero_of_lt (polynomialEmbedding K) S.F S.selected
         gamma w (w + 1 + delay) (S.degree_le gamma hGamma)
         (S.solution gamma hGamma) (by omega)
     have hcount := component_secondTail_card_le_mod B C Gamma
       (selectedPoint (polynomialEmbedding K) S.selected)
       (selectedPoint_injective (polynomialEmbedding K) S.selected)
       (laterTail_in_reduced_delay_secondFlag S C delay hdelay) htail hzero
     have hscale : B.weightedCost (delay • secondFlag) C =
         delay * B.weightedCost secondFlag C := by
       simp only [PrimeFlagBudgetFamily.weightedCost, nsmul_zOnly, nsmul_yz,
         nsmul_all]
       ring
     rw [hscale] at hcount
     exact ⟨delay, hdelay, hdelayMu, htail,
       hcount.trans (Nat.mul_le_mul_right (B.weightedCost secondFlag C) hdelayMu)⟩
   · exact Or.inr htangent
 have providerDichotomy :=
   loosenStageGeneral_dichotomy_with_tangent S hfirstProper B tangentCount
 refine ⟨{
   budgetFamily := B
   multiplicity := multiplicity
   cost := fun C => multiplicity C * B.weightedCost secondFlag C
   one_le_multiplicity := hone
   tangentYZGate := htangentGate
   cost_le := fun _ => le_rfl
   divisor_le :=
     (transportedWeightedResultantsGeneral S hfirstProper hflagChar hmixed).divisor_le
       B multiplicity
   componentBound := ?_
   dichotomy := providerDichotomy }⟩
 intro C
 rcases branchBound C with hproper | htangent
 · obtain ⟨_delay, _hdelay, _hdelayMu, _htail, hcount⟩ := hproper
   exact hcount
 · calc
     (componentSeeds (GenericField K) S.G T H Gamma
         (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
         (stageErrorCap + 1) * B.yzCost C := tangentCount C htangent
     _ ≤ B.weightedCost secondFlag C :=
       yzCost_mul_le_weightedCost B secondFlag C (stageErrorCap + 1) htangentGate
     _ = 1 * B.weightedCost secondFlag C := by simp
     _ ≤ multiplicity C * B.weightedCost secondFlag C :=
       Nat.mul_le_mul_right (B.weightedCost secondFlag C) (hone C)

/- Backward-compatible accepted-row entry point. -/
theorem exists_delayedTailMultiplicityProvider_of_reduced
   {a b s : ℕ}
   (S : ResidualStage (polynomialEmbedding K) Gamma x p errors flag w
     (support a b s))
   (hs : (support a b s).s ≤ fixedSupport.s)
   (hys : (support a b s).ys ≤ fixedSupport.ys)
   (htotal : (support a b s).total ≤ fixedSupport.total)
   (hfirstProper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w + 1))
   (hflagChar : flag.yz + flag.all < p ∧ flag.all < p ∧
     flag.zOnly + flag.yz + flag.all < p)
   (hmixed : (1 + (w + 1) * (2 * (b + s + 3) - 2)) * flag.all +
     (flag.yz + flag.all) * ((2 * (s + 2) - 2) * (w + 1)) < p)
   (bound seedCap slopeCap : ℕ)
   (hnodes : S.nodes.card = agreements + errors)
   (hagreement : ∀ gamma ∈ Gamma, agreements ≤ (S.agreementFiber gamma).card)
   (hshort : w + 1 ≤ bound) (hchar : bound < p)
   (hbox : S.F ∈ globalCoefficientBox K bound w seedCap slopeCap)
   (htangentGate : errors + 1 ≤
     (reducedResidualAgreementFlag (support a b s) (w + 2)).yz) :
   Nonempty (DelayedTailMultiplicityProvider
     (tailFlag1 := reducedResidualAgreementFlag (support a b s) (w + 1))
     (tailFlag2 := reducedResidualAgreementFlag (support a b s) (w + 2)) S) := by
 exact exists_delayedTailMultiplicityProvider_of_reducedGeneral agreements S
   hfirstProper hflagChar hmixed bound seedCap slopeCap hnodes hagreement
   (by norm_num [agreements, errors, n, w]) hshort hchar hbox htangentGate

end
end ProximityPrize.SubmissionLower.RCN335
