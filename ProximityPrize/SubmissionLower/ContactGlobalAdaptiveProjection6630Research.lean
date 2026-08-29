import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6630Research
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6630Research
import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies6630Research

/-!
# End-to-end score-66.30 selected count from adaptive YZ projection families

This module joins the actual positive-`R` factor decomposition, cumulative
geometric flags, canonical residual stages, recursive adaptive YZ projection
budgets, and the tight singular branch. Its only remaining input is an adaptive
YZ projection family at every terminal proper cut.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6630Research

open scoped Classical
open ContactParameters6630Research
open ContactGenericInitialPoint ContactPrimeSeedIncidence
open ContactOriginalRegularSeedCount
open ContactOriginalRegularResidualStage6630Research
open ContactRegularFactorFlag6630Research ContactRegularSeeds6630Research
open ContactGlobalSelectedFamilies6630Research
open ContactRegularFactorResidualStage6630Research
open ContactAdaptiveProjectionFactorProvider6630Research
open ContactTerminalAdaptiveProjection6630Research
open ContactIdentityResidualIteration6630Research
open ContactNearPencil6630FactorLedgerResearch
open ContactInterpolation ContactTranslation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

variable {K Iota : Type} [Field K] [CharP K prime]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)
local instance : CharP (GenericField K) prime := genericField_charP K prime

/-- One actual global regular factor receives its exact cumulative factor
ledger once all canonical geometric stages have adaptive YZ families. -/
theorem regular_factor_seed_bound_of_adaptive_projection_families
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsharp : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : RegularIndex Q)
    (hprojection : ∀ g : GeometricFactor K R.1,
      TerminalAdaptiveProjectionFamiliesYZ6630
        (regularGeometricResidualStage6630 Q hQ hbox hsharp selected Gamma nodes
          x u0 u1 hinj hdegree hnoPencil R g)) :
    (regularSeeds6630 Q selected Gamma R).card * gap ^ 2 ≤
      factorRegularLedgerYZ (regularFlag6630 Q R) := by
  apply regular_factor_seed_bound_of_geometric_counts6630 Q hQ hbox
    selected Gamma R
  intro g
  let S := regularGeometricResidualStage6630 Q hQ hbox hsharp selected Gamma nodes
    x u0 u1 hinj hdegree hnoPencil R g
  have hgeomSub : geometricSeeds K R.1 selected
      (regularSeeds6630 Q selected Gamma R) g ⊆ Gamma :=
    (geometricSeeds_subset K R.1 selected
      (regularSeeds6630 Q selected Gamma R) g).trans
      (regularSeeds6630_subset Q selected Gamma R)
  have hnodesS : S.nodes.card = n := by
    simpa [S, regularGeometricResidualStage6630,
      geometricResidualStage6630] using hnodes
  have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
      (regularSeeds6630 Q selected Gamma R) g,
      agreements ≤ (S.agreementFiber gamma).card := by
    intro gamma hgamma
    simpa [S, ResidualStage6630.agreementFiber, ResidualStage6630.Agrees,
      regularGeometricResidualStage6630, geometricResidualStage6630] using
        hagreement gamma (hgeomSub hgamma)
  exact recursive_scaled_factor_6630_of_adaptive_projection_families_yz
    (polynomialEmbedding_injective K) S hnodesS hagreementS (hprojection g)

/-- Full actual selected-family count. Covering, singular seeds, recursive
identity residualization, cumulative geometric/original factor aggregation,
and strict score-66.30 arithmetic are internal. -/
theorem global_count_lt_alignment_of_adaptive_projection_families
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (hsharp : Q ∈ ContactFlagInterpolation6641Research.globalCoefficientBox
      K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma Q = 0)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (hprojection : ∀ (R : RegularIndex Q) (g : GeometricFactor K R.1),
      TerminalAdaptiveProjectionFamiliesYZ6630
        (regularGeometricResidualStage6630 Q hQ hbox hsharp selected Gamma nodes
          x u0 u1 hinj hdegree hnoPencil R g)) :
    Gamma.card < alignmentBudget := by
  apply global_count_lt_alignment_of_regular_factors Q hQ hbox hsharp selected
    Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
  intro R
  exact regular_factor_seed_bound_of_adaptive_projection_families
    Q hQ hbox hsharp selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
      hnoPencil R (hprojection R)

end

end ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6630Research
