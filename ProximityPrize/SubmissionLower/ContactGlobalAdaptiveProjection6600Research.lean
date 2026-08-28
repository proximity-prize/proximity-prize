import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAdaptiveProjectionFactorProvider6600Research
import ProximityPrize.SubmissionLower.ContactRegularFactorResidualStage6600Research

/-!
# End-to-end score-66 selected count from adaptive projection families

This module joins the actual positive-`R` factor decomposition, its geometric
surface factors, canonical residual stages, recursive adaptive projection
budgets, the rectangular factor ledger, and the unconditional singular
branch.  The only remaining input is the construction of an adaptive unit
projection family at every terminal proper cut.
-/

namespace ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6600Research

open scoped Classical
open ContactParameters6600Research
open ContactGenericInitialPoint ContactPrimeSeedIncidence
open ContactOriginalRegularSeedCount ContactOriginalRegularResidualStage6600Research
open ContactRegularFactorFlag6600Research ContactGlobalSelectedFamilies6600Research
open ContactRegularFactorResidualStage6600Research
open ContactAdaptiveProjectionFactorProvider6600Research
open ContactIdentityResidualIterationResearch
open ContactNearPencil6600FactorLedgerResearch
open ContactInterpolation ContactTranslation

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 35000

variable {K Iota : Type} [Field K] [CharP K prime]

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq Iota := Classical.decEq Iota
local instance : DecidableEq (GenericField K) := Classical.decEq (GenericField K)
local instance : CharP (GenericField K) prime := genericField_charP K prime

/-- One actual global regular factor receives its exact factor ledger once
all of its canonical geometric stages have adaptive projection families. -/
theorem regular_factor_seed_bound_of_adaptive_projection_families
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset Iota) (x u0 u1 : Iota → K)
    (hinj : Set.InjOn x nodes) (hnodes : nodes.card = n)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma,
      agreements ≤ (nodes.filter (fun i ↦
        (selected gamma).eval (x i) = u0 i + gamma * u1 i)).card)
    (hnoPencil : NoLargeSelectedPencil selected Gamma w errors)
    (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
    (hprojection : ∀ g : GeometricFactor K R.1,
      TerminalAdaptiveProjectionFamilies
        (regularGeometricResidualStage Q hQ hbox selected Gamma nodes
          x u0 u1 hinj hdegree hnoPencil R g)) :
    (regularSeeds Q selected Gamma R).card * gap ^ 2 ≤
      factorRegularLedger (regularFlag Q R) := by
  apply regular_factor_seed_bound_of_geometric_counts Q hQ hbox
    selected Gamma R
  intro g
  let S := regularGeometricResidualStage Q hQ hbox selected Gamma nodes
    x u0 u1 hinj hdegree hnoPencil R g
  have hgeomSub : geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g ⊆ Gamma :=
    (geometricSeeds_subset K R.1 selected
      (regularSeeds Q selected Gamma R) g).trans
      (regularSeeds_subset Q selected Gamma R)
  have hnodesS : S.nodes.card = n := by
    simpa [S, regularGeometricResidualStage, geometricResidualStage] using hnodes
  have hagreementS : ∀ gamma ∈ geometricSeeds K R.1 selected
      (regularSeeds Q selected Gamma R) g,
      agreements ≤ (S.agreementFiber gamma).card := by
    intro gamma hgamma
    simpa [S, ResidualStage.agreementFiber, ResidualStage.Agrees,
      regularGeometricResidualStage, geometricResidualStage] using
        hagreement gamma (hgeomSub hgamma)
  exact recursive_scaled_factor_6600_of_adaptive_projection_families
    (polynomialEmbedding_injective K) S hnodesS hagreementS (hprojection g)

/-- Full actual selected-family count.  Covering, singular seeds, recursive
identity residualization, geometric/original factor aggregation, and the
strict score-66 arithmetic are all internal. -/
theorem global_count_lt_alignment_of_adaptive_projection_families
    (Q : MvPolynomial (Fin 4) K) (hQ : Q ≠ 0)
    (hbox : Q ∈ globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
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
    (hprojection : ∀
      (R : ContactRegularFactorFlag6600Research.RegularIndex Q)
      (g : GeometricFactor K R.1),
      TerminalAdaptiveProjectionFamilies
        (regularGeometricResidualStage Q hQ hbox selected Gamma nodes
          x u0 u1 hinj hdegree hnoPencil R g)) :
    Gamma.card < alignmentBudget := by
  apply global_count_lt_alignment_of_regular_factors Q hQ hbox selected
    Gamma nodes x u0 u1 hinj hnodes hdegree hsolution hagreement hnoPencil
  intro R
  exact regular_factor_seed_bound_of_adaptive_projection_families
    Q hQ hbox selected Gamma nodes x u0 u1 hinj hnodes hdegree hagreement
      hnoPencil R (hprojection R)

end

end ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6600Research

#print axioms ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6600Research.regular_factor_seed_bound_of_adaptive_projection_families
#print axioms ProximityPrize.SubmissionLower.ContactGlobalAdaptiveProjection6600Research.global_count_lt_alignment_of_adaptive_projection_families
