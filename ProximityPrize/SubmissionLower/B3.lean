import ProximityPrize.SubmissionLower.GX
import ProximityPrize.SubmissionLower.P7
namespace ProximityPrize.SubmissionLower.ContactDelayedTailMultiplicityProvider6732Research
open scoped Classical BigOperators
open ContactIdentityResidualIterationResearch ContactGenericSurface
open ContactPrimeSeedIncidence ContactRegularComponentCover
open ContactProperCutSeedCount
open ContactFirstTailCertificate6731Research
open ContactFlagBezout6543Research ContactPrimeFlagBudgetFamilyResearch
open ContactTwoTailMultiplicityAggregation6732Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {pchar errors w:ℕ} [CharP Omega pchar]
variable {flag tailFlag1 tailFlag2:FlagDegree}
variable {support:ContactResidualSupportParametersResearch.ResidualSupportParameters}
abbrev FirstTailComponent
   (S:ResidualStage phi Gamma x pchar errors flag w support):=
 RegularComponent Omega S.G (globalTailCut phi S.F (w+1))
   (regularitySurface phi S.F)
structure DelayedTailMultiplicityProvider
   (S:ResidualStage phi Gamma x pchar errors flag w support) where
 budgetFamily:PrimeFlagBudgetFamily
   (G:=S.G) (T:=globalTailCut phi S.F (w+1))
   (H:=regularitySurface phi S.F) flag tailFlag1
 multiplicity:FirstTailComponent S → ℕ
 cost:FirstTailComponent S → ℕ
 one_le_multiplicity:∀ C,1 ≤ multiplicity C
 tangentYZGate:errors+1 ≤ tailFlag2.yz
 cost_le:∀ C,
   cost C ≤ multiplicity C*budgetFamily.weightedCost tailFlag2 C
 divisor_le:
   (∑ C,multiplicity C*budgetFamily.weightedCost tailFlag2 C) ≤
     flagMixed flag tailFlag1 tailFlag2
 componentBound:∀ C,
   (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
     (regularitySurface phi S.F) Gamma
     (selectedPoint phi S.selected) C).card ≤ cost C
 dichotomy:∀ C,
   (∃ delay,1 ≤ delay∧delay ≤ multiplicity C∧
     globalTailCut phi S.F (w+1+delay)∉C.1)∨
   ((∀ delay,globalTailCut phi S.F (w+1+delay)∈C.1)∧
     (componentSeeds Omega S.G (globalTailCut phi S.F (w+1))
       (regularitySurface phi S.F) Gamma
       (selectedPoint phi S.selected) C).card ≤
         (errors+1)*budgetFamily.yzCost C)
theorem stage_card_le_flagMixed
   (S:ResidualStage phi Gamma x pchar errors flag w support)
   (P:DelayedTailMultiplicityProvider
     (tailFlag1:=tailFlag1) (tailFlag2:=tailFlag2) S):
   Gamma.card ≤ flagMixed flag tailFlag1 tailFlag2:=by
 classical
 let T1:=globalTailCut phi S.F (w+1)
 let H:=regularitySurface phi S.F
 let point:=selectedPoint phi S.selected
 have hG:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) S.G=0:=S.on_component
 have hT1:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) T1=0:=by
   intro gamma hgamma
   exact selected_globalTailCut_zero phi S.F S.selected gamma w
     (S.degree_le gamma hgamma) (S.solution gamma hgamma)
 have hH:∀ gamma∈Gamma,
     MvPolynomial.eval (point gamma) H≠0:=by
   intro gamma hgamma
   exact selectedPoint_evaluation phi S.selected gamma
     (MvPolynomial.pderiv (2:Fin 4) S.F) |>.symm ▸ S.regular gamma hgamma
 have hcover:Gamma.card ≤
     ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=
   card_le_sum_componentSeeds Omega S.G T1 H Gamma point hG hT1 hH
 calc
   Gamma.card ≤ ∑ C:RegularComponent Omega S.G T1 H,
       (componentSeeds Omega S.G T1 H Gamma point C).card:=hcover
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,P.cost C:=
     Finset.sum_le_sum (fun C _↦P.componentBound C)
   _ ≤ ∑ C:RegularComponent Omega S.G T1 H,
       P.multiplicity C*P.budgetFamily.weightedCost tailFlag2 C:=
     Finset.sum_le_sum (fun C _↦P.cost_le C)
   _ ≤ flagMixed flag tailFlag1 tailFlag2:=P.divisor_le
end
end ProximityPrize.SubmissionLower.ContactDelayedTailMultiplicityProvider6732Research
