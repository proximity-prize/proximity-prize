import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidenceResearch
import ProximityPrize.SubmissionLower.ContactIdentityResidualCurveIteration6630Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag6630Research

/-!
# Recursive incidence on an arbitrary regular curve prime

The outer surface incidence decomposes a proper agreement cut into regular
curve primes.  Actual identity nodes can then appear again on one such
prime after residualization.  `CurveResidualStage6630` transports the arbitrary
prime through every residual coordinate change and terminates in the exact
dichotomy needed here:

* every remaining agreement cut is proper on the terminal prime; or
* more identities remain than the residual degree, so the selected family
  has already entered the no-large-pencil tail.

This module performs all finite incidence bookkeeping across that recursive
inner process.  The only geometric input in the proper branch is a terminal
fiber bound affine in the terminal residual degree.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research

open scoped Classical
open ContactGenericSurface ContactPolynomialSolutions ContactTranslation
open ContactTaylorNumerators
open ContactPrimeSeedIncidence ContactIncidence
open ContactIdentityResidualCurveIteration6630Research
open ContactIdentityResidualCurveIteration6630Research.CurveResidualStage6630
open ContactNearPencilStratifiedIncidenceResearch
open ContactNearPencil6600ArithmeticResearch
open ContactResidualSparseComponentAdapterResearch
open ContactFlagBezout6543Research
open ContactIdentityResidualGlobalFlagResearch
open ContactIdentityResidualGlobalFlag6630Research
open ContactNearPencil6630FlagResearch
open ContactIdentityResidualIncidenceResearch
open ContactIdentityResidualZeroBudgetTransportResearch

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option autoImplicit false

variable {K Omega Iota : Type} [Field K] [Field Omega] [IsAlgClosed Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {p e : ℕ} [CharP Omega p]
variable {surfaceFlag cutFlag : FlagDegree}

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Omega := Classical.decEq Omega
local instance : DecidableEq Iota := Classical.decEq Iota


/-- Agreement support for a current residual surface at the 66.30 caps.
The zero/zero/one global residual transform is the identity. -/
theorem surfaceMap_agreement_in_flag_of_surface_weights6630
    (F : MvPolynomial (Fin 4) K)
    (hS : ContactPost6464MinkowskiRecurrenceResearch.wt
      residualSWeights F ≤ 8)
    (hYS : ContactPost6464MinkowskiRecurrenceResearch.wt
      residualYSWeights F ≤ 40)
    (hTotal : ContactPost6464MinkowskiRecurrenceResearch.wt
      residualTotalWeights F ≤ 617)
    (d : ℕ) (coeffs : ℕ → K) (x0 u0 u1 : K) :
    PolynomialInFlag (residualAgreementFlag6630 d)
      (surfaceMap phi (agreementNumerator F d coeffs x0 u0 u1)) := by
  have h := surfaceMap_globalResidual_agreement_in_flag6630
    phi (0 : Polynomial K) 0 1 F hS hYS hTotal d coeffs x0 u0 u1
  simpa only [
    ContactIdentityResidualIncidenceResearch.globalResidualHom_zero_zero_one]
    using h

/-- Inner recursive incidence with an abstract proper-terminal fiber bound.

`hlarge` is deliberately branch-local.  In the intended application its
charge is the original component's `Z` degree: a many-identity terminal
stage forces `Z` to be transcendental, while the residual automorphism fixes
`Z`.  Keeping exactly that implication explicit avoids assuming that every
regular component is `Z`-transcendental.
-/
theorem recursive_curve_stratified_incidence_bound
    (hphi : Function.Injective phi) {d a : ℕ}
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (degreeCost unitCost U V zCharge : ℕ)
    (hda : d < a)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hfiber : ∀ D : S.TerminalDescendant,
      D.stage.identities = ∅ → ∀ i ∈ D.stage.nodes,
        (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
          D.degree * degreeCost + unitCost)
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card * (a - d) ≤ (e + 1) * (a - d) * zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * degreeCost + V * unitCost + (e + 1) * (a - d) * zCharge := by
  classical
  obtain ⟨D⟩ := S.exists_terminal_descendant hphi
  rcases D.terminal with hproper | hpencil
  · let k := d - D.degree
    have hk : k ≤ d := Nat.sub_le d D.degree
    have hDle : D.degree ≤ d := D.degree_le
    have hdegreeEq : D.degree = d - k := by
      dsimp only [k]
      omega
    have hnodeEq : D.stage.nodes.card = S.nodes.card - k := by
      simpa only [k] using D.nodes_card
    have hterminalAgreement : ∀ gamma ∈ Gamma,
        a - k ≤ (D.stage.agreementFiber gamma).card := by
      intro gamma hgamma
      exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
        (by simpa only [k] using D.agreement_card gamma hgamma)
    have hterminalFiber : ∀ i ∈ D.stage.nodes,
        (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
          D.degree * degreeCost + unitCost := by
      intro i hi
      exact hfiber D hproper i hi
    have hrawTerminal := incidence_after_exempt_nodes
      (fun gamma i ↦ D.stage.Agrees gamma i)
      Gamma D.stage.nodes ∅ (a - k)
        (D.degree * degreeCost + unitCost)
      (by simp) hterminalAgreement (by
        intro i hi
        exact hterminalFiber i (by simpa using hi))
    have hraw : Gamma.card * (a - k) ≤
        (S.nodes.card - k) * ((d - k) * degreeCost + unitCost) := by
      simpa only [Finset.card_empty, Nat.sub_zero, hnodeEq, hdegreeEq] using
        hrawTerminal
    have hmain : Gamma.card * (a - d) ≤
        U * degreeCost + V * unitCost :=
      stratified_incidence_linear Gamma.card S.nodes.card a d k
        degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
    exact hmain.trans (Nat.le_add_right _ _)
  · have htail := hlarge D hpencil.1
    exact htail.trans (Nat.le_add_left _ _)

/-- Concrete terminal wrapper: a finite-zero-set theorem on every proper
terminal agreement polynomial supplies the affine terminal fiber premise.
All selected-point injectivity and evaluation facts are discharged here.
-/
theorem recursive_curve_stratified_incidence_of_zero_bounds
    (hphi : Function.Injective phi) {d a : ℕ}
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (degreeCost unitCost U V zCharge : ℕ)
    (hda : d < a)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hzero : ∀ D : S.TerminalDescendant,
      D.stage.identities = ∅ → ∀ i ∈ D.stage.nodes,
        FiniteZeroSetBound D.stage.primeIdeal
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i))
          (D.degree * degreeCost + unitCost))
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card * (a - d) ≤ (e + 1) * (a - d) * zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * degreeCost + V * unitCost + (e + 1) * (a - d) * zCharge := by
  apply recursive_curve_stratified_incidence_bound hphi S
    degreeCost unitCost U V zCharge hda hagreement
  · intro D hterminal i hi
    exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
      D.stage.F D.stage.selected Gamma p D.degree
      D.stage.characteristic_bound D.stage.degree_le D.stage.solution
      D.stage.regular D.stage.on_prime
      (x i) (D.stage.u0 i) (D.stage.u1 i)
      (D.degree * degreeCost + unitCost)
      (hzero D hterminal i hi)
  · exact hlarge
  · exact hdegree
  · exact hunit

/-- End-to-end recursive inner incidence from one original per-prime flag
budget.  The invariant theorem carries that *same* cost through every
component-specific residual path; no whole-component budget is rebuilt at
the transformed stages.  This is what keeps the eventual global sum over
the original regular components valid.
-/
theorem recursive_curve_stratified_incidence_of_prime_flag_budget
    (hphi : Function.Injective phi) {d a : ℕ}
    (S : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag d)
    (cost : FlagDegree → ℕ)
    (B : PrimeFlagZeroBudget S.primeIdeal cost)
    (degreeCost unitCost U V zCharge : ℕ)
    (hcost : ∀ t : ℕ,
      cost (residualAgreementFlag6630 t) = t * degreeCost + unitCost)
    (hda : d < a)
    (hagreement : ∀ gamma ∈ Gamma,
      a ≤ (S.agreementFiber gamma).card)
    (hlarge : ∀ D : S.TerminalDescendant,
      D.degree < D.stage.identities.card →
        Gamma.card * (a - d) ≤ (e + 1) * (a - d) * zCharge)
    (hdegree : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) * (d - k) ≤ U * (a - k))
    (hunit : ∀ k ≤ d,
      (S.nodes.card - k) * (a - d) ≤ V * (a - k)) :
    Gamma.card * (a - d) ≤
      U * degreeCost + V * unitCost + (e + 1) * (a - d) * zCharge := by
  classical
  let Inv : ∀ n, CurveResidualStage6630 phi Gamma x p e
      surfaceFlag cutFlag n → Prop :=
    fun _ A ↦ PrimeFlagZeroBudget A.primeIdeal cost
  have htransport : ∀ {n m}
      {A : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag n}
      {Anext : CurveResidualStage6630 phi Gamma x p e surfaceFlag cutFlag m},
      A.ResidualTransition Anext → Inv n A → Inv m Anext := by
    intro n m A Anext htransition hbudget
    obtain ⟨aY, v, bY, aS, bS, cS, hv, _, _, hprime⟩ := htransition
    dsimp only [Inv] at hbudget ⊢
    rw [hprime]
    exact hbudget.mapResidual aY v bY aS bS cS hv
  obtain ⟨D, hDBudget⟩ := S.exists_terminal_descendant_with_invariant
    hphi Inv htransport B
  rcases D.terminal with hproper | hpencil
  · let k := d - D.degree
    have hk : k ≤ d := Nat.sub_le d D.degree
    have hDle : D.degree ≤ d := D.degree_le
    have hdegreeEq : D.degree = d - k := by
      dsimp only [k]
      omega
    have hnodeEq : D.stage.nodes.card = S.nodes.card - k := by
      simpa only [k] using D.nodes_card
    have hterminalAgreement : ∀ gamma ∈ Gamma,
        a - k ≤ (D.stage.agreementFiber gamma).card := by
      intro gamma hgamma
      exact (Nat.sub_le_sub_right (hagreement gamma hgamma) k).trans
        (by simpa only [k] using D.agreement_card gamma hgamma)
    have hterminalFiber : ∀ i ∈ D.stage.nodes,
        (Gamma.filter (fun gamma ↦ D.stage.Agrees gamma i)).card ≤
          D.degree * degreeCost + unitCost := by
      intro i hi
      have hflag : PolynomialInFlag (residualAgreementFlag6630 D.degree)
          (agreementPolynomial phi D.stage.F D.degree
            (x i) (D.stage.u0 i) (D.stage.u1 i)) :=
        surfaceMap_agreement_in_flag_of_surface_weights6630
          D.stage.F D.stage.surface_s_weight D.stage.surface_ys_weight
          D.stage.surface_total_weight D.degree
          (fun j ↦ (j.factorial : K)⁻¹)
          (x i) (D.stage.u0 i) (D.stage.u1 i)
      have hzero := hDBudget.zero_le (residualAgreementFlag6630 D.degree)
        (agreementPolynomial phi D.stage.F D.degree
          (x i) (D.stage.u0 i) (D.stage.u1 i))
        hflag (D.stage.proper_agreement_of_terminal hproper hi)
      rw [hcost D.degree] at hzero
      exact agreement_fiber_card_le_of_zero_bound phi D.stage.primeIdeal
        D.stage.F D.stage.selected Gamma p D.degree
        D.stage.characteristic_bound D.stage.degree_le D.stage.solution
        D.stage.regular D.stage.on_prime
        (x i) (D.stage.u0 i) (D.stage.u1 i)
        (D.degree * degreeCost + unitCost) hzero
    have hrawTerminal := incidence_after_exempt_nodes
      (fun gamma i ↦ D.stage.Agrees gamma i)
      Gamma D.stage.nodes ∅ (a - k)
        (D.degree * degreeCost + unitCost)
      (by simp) hterminalAgreement (by
        intro i hi
        exact hterminalFiber i (by simpa using hi))
    have hraw : Gamma.card * (a - k) ≤
        (S.nodes.card - k) * ((d - k) * degreeCost + unitCost) := by
      simpa only [Finset.card_empty, Nat.sub_zero, hnodeEq, hdegreeEq] using
        hrawTerminal
    have hmain : Gamma.card * (a - d) ≤
        U * degreeCost + V * unitCost :=
      stratified_incidence_linear Gamma.card S.nodes.card a d k
        degreeCost unitCost U V hk hda hraw (hdegree k hk) (hunit k hk)
    exact hmain.trans (Nat.le_add_right _ _)
  · have htail := hlarge D hpencil.1
    exact htail.trans (Nat.le_add_left _ _)

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research.recursive_curve_stratified_incidence_bound
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research.recursive_curve_stratified_incidence_of_zero_bounds
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualCurveTerminalIncidence6630Research.recursive_curve_stratified_incidence_of_prime_flag_budget
