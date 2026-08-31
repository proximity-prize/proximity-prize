import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIterationResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualIncidenceResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualZeroBudgetTransportResearch
import ProximityPrize.SubmissionLower.ContactNearPencilStratifiedIncidenceResearch
import ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapterResearch
namespace ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidenceResearch
open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactPrimeSeedIncidence ContactIncidence
open ContactIdentityResidualCurveIterationResearch
open ContactIdentityResidualCurveIterationResearch.CurveResidualStage
open ContactNearPencilStratifiedIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactResidualSparseComponentAdapterResearch
open ContactFlagBezout6543Research
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualIncidenceResearch
open ContactIdentityResidualZeroBudgetTransportResearch
open ContactResidualSupportParametersResearch
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
variable {K Omega Iota:Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi:Polynomial K →+*Omega} {Gamma:Finset K} {x:Iota → K}
variable {p e:ℕ} [CharP Omega p]
variable {surfaceFlag cutFlag:FlagDegree}
variable {support:ResidualSupportParameters}
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Omega:=Classical.decEq Omega
local instance:DecidableEq Iota:=Classical.decEq Iota
theorem recursive_curve_stratified_incidence_bound
    (hphi:Function.Injective phi) {d a:ℕ}
    (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (degreeCost unitCost U V zCharge:ℕ)
    (hda:d < a)
    (hagreement:∀ gamma∈Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hfiber:∀ D:S.TerminalDescendant,
      D.stage.identities=∅ → ∀ i∈D.stage.nodes,
        (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
          D.degree*degreeCost+unitCost)
    (hlarge:∀ D:S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
    (hdegree:∀ k ≤ d,
      (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
    (hunit:∀ k ≤ d,
      (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
    Gamma.card*(a-d) ≤
      U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
  classical
  obtain ⟨D⟩:=S.exists_terminal_descendant hphi
  rcases D.terminal with hproper | hpencil
  · let k:=d-D.degree
    have hk:k ≤ d:=Nat.sub_le d D.degree
    have hDle:D.degree ≤ d:=D.degree_le
    have hdegreeEq:D.degree=d-k:=by
      dsimp only [k]
      omega
    have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
      simpa only [k] using D.nodes_card
    have hterminalAgreement:∀ gamma∈Gamma,
        a-k ≤ (D.stage.agreementFiber gamma).card:=by
      intro gamma hgamma
      exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
        (by simpa only [k] using D.agreement_card gamma hgamma)
    have hterminalFiber:∀ i∈D.stage.nodes,
        (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
          D.degree*degreeCost+unitCost:=by
      intro i hi
      exact hfiber D hproper i hi
    have hrawTerminal:=incidence_after_exempt_nodes
      (fun gamma i↦D.stage.Agrees gamma i)
      Gamma D.stage.nodes ∅ (a-k)
        (D.degree*degreeCost+unitCost)
      (by simp) hterminalAgreement (by
        intro i hi
        exact hterminalFiber i (by simpa using hi))
    have hraw:Gamma.card*(a-k) ≤
        (S.nodes.card-k)*((d-k)*degreeCost+unitCost):=by
      simpa only [Finset.card_empty,Nat.sub_zero,hnodeEq,hdegreeEq] using
        hrawTerminal
    have hmain:Gamma.card*(a-d) ≤
        U*degreeCost+V*unitCost:=
      stratified_incidence_linear Gamma.card S.nodes.card a d k
        degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
    exact hmain.trans (Nat.le_add_right _ _)
  · have htail:=hlarge D hpencil.1
    exact htail.trans (Nat.le_add_left _ _)
theorem recursive_curve_stratified_incidence_of_zero_bounds
    (hphi:Function.Injective phi) {d a:ℕ}
    (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (degreeCost unitCost U V zCharge:ℕ)
    (hda:d < a)
    (hagreement:∀ gamma∈Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hzero:∀ D:S.TerminalDescendant,
      D.stage.identities=∅ → ∀ i∈D.stage.nodes,
        FiniteZeroSetBound D.stage.primeIdeal
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (D.degree*degreeCost+unitCost))
    (hlarge:∀ D:S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
    (hdegree:∀ k ≤ d,
      (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
    (hunit:∀ k ≤ d,
      (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
    Gamma.card*(a-d) ≤
      U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
  apply recursive_curve_stratified_incidence_bound hphi S
    degreeCost unitCost U V zCharge hda hagreement
  · intro D hterminal i hi
    exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
      D.stage.F D.stage.selected Gamma p D.degree
      D.stage.characteristic_bound D.stage.degree_le D.stage.solution
      D.stage.regular D.stage.on_prime
      (x i) (D.stage.u0 i) (D.stage.u1 i)
      (D.degree*degreeCost+unitCost)
      (hzero D hterminal i hi)
  · exact hlarge
  · exact hdegree
  · exact hunit
theorem recursive_curve_stratified_incidence_of_prime_flag_budget
    (hphi:Function.Injective phi) {d a:ℕ}
    (S:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag d support)
    (cost:FlagDegree → ℕ)
    (B:PrimeFlagZeroBudget S.primeIdeal cost)
    (degreeCost unitCost U V zCharge:ℕ)
    (hcost:∀ t:ℕ,
      cost (support.residualAgreementFlag t)=t*degreeCost+unitCost)
    (hda:d < a)
    (hagreement:∀ gamma∈Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hlarge:∀ D:S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card*(a-d) ≤ (e+1)*(a-d)*zCharge)
    (hdegree:∀ k ≤ d,
      (S.nodes.card-k)*(a-d)*(d-k) ≤ U*(a-k))
    (hunit:∀ k ≤ d,
      (S.nodes.card-k)*(a-d) ≤ V*(a-k)):
    Gamma.card*(a-d) ≤
      U*degreeCost+V*unitCost+(e+1)*(a-d)*zCharge:=by
  classical
  let Inv:∀ n,CurveResidualStage phi Gamma x p e
      surfaceFlag cutFlag n support → Prop:=
    fun _ A↦PrimeFlagZeroBudget A.primeIdeal cost
  have htransport:∀ {n m}
      {A:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag n support}
      {Anext:CurveResidualStage phi Gamma x p e surfaceFlag cutFlag m support},
      A.ResidualTransition Anext → Inv n A → Inv m Anext:=by
    intro n m A Anext htransition hbudget
    obtain ⟨aY,v,bY,aS,bS,cS,hv,_,_,hprime⟩:=htransition
    dsimp only [Inv] at hbudget ⊢
    rw [hprime]
    exact hbudget.mapResidual aY v bY aS bS cS hv
  obtain ⟨D,hDBudget⟩:=S.exists_terminal_descendant_with_invariant
    hphi Inv htransport B
  rcases D.terminal with hproper | hpencil
  · let k:=d-D.degree
    have hk:k ≤ d:=Nat.sub_le d D.degree
    have hDle:D.degree ≤ d:=D.degree_le
    have hdegreeEq:D.degree=d-k:=by
      dsimp only [k]
      omega
    have hnodeEq:D.stage.nodes.card=S.nodes.card-k:=by
      simpa only [k] using D.nodes_card
    have hterminalAgreement:∀ gamma∈Gamma,
        a-k ≤ (D.stage.agreementFiber gamma).card:=by
      intro gamma hgamma
      exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
        (by simpa only [k] using D.agreement_card gamma hgamma)
    have hterminalFiber:∀ i∈D.stage.nodes,
        (Gamma.filter (fun gamma↦D.stage.Agrees gamma i)).card ≤
          D.degree*degreeCost+unitCost:=by
      intro i hi
      have hflag:PolynomialInFlag (support.residualAgreementFlag D.degree)
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i)):=
        surfaceMap_agreement_in_flag_of_support support
          D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
          D.stage.surface_total_weight D.degree
          (fun j↦(j.factorial:K)⁻¹)
          (x i) (D.stage.u0 i) (D.stage.u1 i)
      have hzero:=hDBudget.zero_le (support.residualAgreementFlag D.degree)
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        hflag (D.stage.proper_agreement_of_terminal hproper hi)
      rw [hcost D.degree] at hzero
      exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
        D.stage.F D.stage.selected Gamma p D.degree
        D.stage.characteristic_bound D.stage.degree_le D.stage.solution
        D.stage.regular D.stage.on_prime
        (x i) (D.stage.u0 i) (D.stage.u1 i)
        (D.degree*degreeCost+unitCost) hzero
    have hrawTerminal:=incidence_after_exempt_nodes
      (fun gamma i↦D.stage.Agrees gamma i)
      Gamma D.stage.nodes ∅ (a-k)
        (D.degree*degreeCost+unitCost)
      (by simp) hterminalAgreement (by
        intro i hi
        exact hterminalFiber i (by simpa using hi))
    have hraw:Gamma.card*(a-k) ≤
        (S.nodes.card-k)*((d-k)*degreeCost+unitCost):=by
      simpa only [Finset.card_empty,Nat.sub_zero,hnodeEq,hdegreeEq] using
        hrawTerminal
    have hmain:Gamma.card*(a-d) ≤
        U*degreeCost+V*unitCost:=
      stratified_incidence_linear Gamma.card S.nodes.card a d k
        degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
    exact hmain.trans (Nat.le_add_right _ _)
  · have htail:=hlarge D hpencil.1
    exact htail.trans (Nat.le_add_left _ _)
end
end ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidenceResearch
